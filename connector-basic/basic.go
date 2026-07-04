/*
 * Licensed to the Apache Software Foundation (ASF) under one
 * or more contributor license agreements.  See the NOTICE file
 * distributed with this work for additional information
 * regarding copyright ownership.  The ASF licenses this file
 * to you under the Apache License, Version 2.0 (the
 * "License"); you may not use this file except in compliance
 * with the License.  You may obtain a copy of the License at
 *
 *   http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing,
 * software distributed under the License is distributed on an
 * "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY
 * KIND, either express or implied.  See the License for the
 * specific language governing permissions and limitations
 * under the License.
 */

package basic

import (
	"context"
	"crypto/rand"
	"crypto/sha256"
	"crypto/tls"
	"embed"
	"encoding/base64"
	"encoding/json"
	"fmt"
	"io"
	"net/http"
	"net/url"
	"regexp"
	"strings"
	"time"
	"unicode/utf8"

	"github.com/apache/answer-plugins/connector-basic/i18n"
	"github.com/apache/answer-plugins/util"
	"github.com/apache/answer/pkg/checker"
	"github.com/apache/answer/plugin"
	"github.com/segmentfault/pacman/log"
	"github.com/tidwall/gjson"
	"golang.org/x/oauth2"
)

var (
	replaceUsernameReg = regexp.MustCompile(`[^a-zA-Z0-9._-]+`)
	//go:embed  info.yaml
	Info embed.FS
)

const (
	cookieState    = "basic_connector_state"
	cookieVerifier = "basic_connector_verifier"
	cookieTTL      = 600 // 10 minutes
	httpTimeout    = 15 * time.Second
)

// ConnectorConfig holds all admin-configurable options.
type ConnectorConfig struct {
	Name string `json:"name"`

	// OIDC auto-discovery — if set, authorize_url / token_url / user_json_url
	// are populated automatically from {issuer}/.well-known/openid-configuration.
	// Manual URL fields below take precedence when both are provided.
	IssuerURL string `json:"issuer_url"`

	ClientID     string `json:"client_id"`
	ClientSecret string `json:"client_secret"`
	AuthorizeUrl string `json:"authorize_url"`
	TokenUrl     string `json:"token_url"`
	UserJsonUrl  string `json:"user_json_url"`

	UserIDJsonPath          string `json:"user_id_json_path"`
	UserDisplayNameJsonPath string `json:"user_display_name_json_path"`
	UserUsernameJsonPath    string `json:"user_username_json_path"`
	UserEmailJsonPath       string `json:"user_email_json_path"`
	UserAvatarJsonPath      string `json:"user_avatar_json_path"`

	CheckEmailVerified    bool   `json:"check_email_verified"`
	EmailVerifiedJsonPath string `json:"email_verified_json_path"`

	Scope   string `json:"scope"`
	LogoSVG string `json:"logo_svg"`

	// Security options
	EnablePKCE    bool `json:"enable_pkce"`
	SkipTLSVerify bool `json:"skip_tls_verify"`
}

// oidcDiscovery holds the endpoints we read from the provider's well-known document.
type oidcDiscovery struct {
	AuthorizationEndpoint string `json:"authorization_endpoint"`
	TokenEndpoint         string `json:"token_endpoint"`
	UserinfoEndpoint      string `json:"userinfo_endpoint"`
}

// tokenExchangeResponse is the minimal shape of a token endpoint JSON response.
type tokenExchangeResponse struct {
	AccessToken string `json:"access_token"`
	IDToken     string `json:"id_token"`
	TokenType   string `json:"token_type"`
}

type Connector struct {
	Config *ConnectorConfig
}

func init() {
	plugin.Register(&Connector{
		Config: &ConnectorConfig{},
	})
}

// ---------------------------------------------------------------------------
// plugin.Connector interface
// ---------------------------------------------------------------------------

func (g *Connector) Info() plugin.Info {
	info := &util.Info{}
	info.GetInfo(Info)

	return plugin.Info{
		Name:        plugin.MakeTranslator(i18n.InfoName),
		SlugName:    info.SlugName,
		Description: plugin.MakeTranslator(i18n.InfoDescription),
		Author:      info.Author,
		Version:     info.Version,
		Link:        info.Link,
	}
}

func (g *Connector) ConnectorLogoSVG() string {
	return g.Config.LogoSVG
}

func (g *Connector) ConnectorName() plugin.Translator {
	if len(g.Config.Name) > 0 {
		return plugin.MakeTranslator(g.Config.Name)
	}
	return plugin.MakeTranslator(i18n.ConnectorName)
}

func (g *Connector) ConnectorSlugName() string {
	return "basic"
}

// ConnectorSender builds the authorization URL.
//
//   - A random state value is always stored in a short-lived cookie for CSRF protection.
//   - When PKCE is enabled a code_verifier is generated, stored in a cookie, and the
//     S256 code_challenge is appended to the authorization URL.
//   - When IssuerURL is set the authorization endpoint is resolved via OIDC discovery.
func (g *Connector) ConnectorSender(ctx *plugin.GinContext, receiverURL string) (redirectURL string) {
	authURL, _, _, err := g.resolveEndpoints()
	if err != nil {
		log.Errorf("basic: resolve endpoints: %v", err)
		return ""
	}
	if authURL == "" {
		log.Errorf("basic: authorize URL is not configured")
		return ""
	}

	state, err := randomToken(16)
	if err != nil {
		log.Errorf("basic: state generation: %v", err)
		return ""
	}
	ctx.SetCookie(cookieState, state, cookieTTL, "/", "", false, true)

	params := url.Values{
		"client_id":     {g.Config.ClientID},
		"redirect_uri":  {receiverURL},
		"response_type": {"code"},
		"state":         {state},
	}
	if g.Config.Scope != "" {
		params.Set("scope", g.Config.Scope)
	}

	if g.Config.EnablePKCE {
		verifier, err := generateCodeVerifier()
		if err != nil {
			log.Errorf("basic: PKCE verifier generation: %v", err)
			return ""
		}
		ctx.SetCookie(cookieVerifier, verifier, cookieTTL, "/", "", false, true)
		params.Set("code_challenge", computeCodeChallenge(verifier))
		params.Set("code_challenge_method", "S256")
	}

	return authURL + "?" + params.Encode()
}

// ConnectorReceiver handles the OAuth2 / OIDC callback:
//  1. Verifies the state cookie (always — CSRF guard).
//  2. Exchanges the authorization code for an access token.
//     When PKCE is enabled the exchange is done via a raw HTTP POST so the
//     code_verifier can be included; otherwise the oauth2 library is used.
//  3. Fetches the user JSON from the configured (or discovered) userinfo URL
//     and extracts fields via gjson paths.
func (g *Connector) ConnectorReceiver(ctx *plugin.GinContext, receiverURL string) (userInfo plugin.ExternalLoginUserInfo, err error) {
	code := ctx.Query("code")

	// CSRF guard — always verify state.
	state := ctx.Query("state")
	savedState, cookieErr := ctx.Cookie(cookieState)
	if cookieErr != nil || savedState != state {
		return userInfo, fmt.Errorf("basic: state mismatch — possible CSRF attack")
	}

	_, tokenURL, discoveredUserInfoURL, err := g.resolveEndpoints()
	if err != nil {
		return userInfo, fmt.Errorf("basic: resolve endpoints: %w", err)
	}

	// Manual user_json_url always wins over the discovered userinfo endpoint.
	userInfoURL := discoveredUserInfoURL
	if g.Config.UserJsonUrl != "" {
		userInfoURL = g.Config.UserJsonUrl
	}

	// ── Token exchange ────────────────────────────────────────────────────────
	var accessToken string

	if g.Config.EnablePKCE {
		verifier, cookieErr := ctx.Cookie(cookieVerifier)
		if cookieErr != nil || verifier == "" {
			return userInfo, fmt.Errorf("basic: PKCE enabled but verifier cookie is missing")
		}
		tokenResp, err := g.exchangeCodeManual(tokenURL, code, verifier, receiverURL)
		if err != nil {
			return userInfo, fmt.Errorf("basic: PKCE token exchange failed: %w", err)
		}
		accessToken = tokenResp.AccessToken
	} else {
		httpCtx := context.WithValue(context.Background(), oauth2.HTTPClient, g.httpClient())
		oauth2Config := &oauth2.Config{
			ClientID:     g.Config.ClientID,
			ClientSecret: g.Config.ClientSecret,
			Endpoint: oauth2.Endpoint{
				AuthURL:   g.Config.AuthorizeUrl,
				TokenURL:  tokenURL,
				AuthStyle: oauth2.AuthStyleAutoDetect,
			},
			RedirectURL: receiverURL,
		}
		token, err := oauth2Config.Exchange(httpCtx, code)
		if err != nil {
			return userInfo, fmt.Errorf("code exchange failed: %s", err.Error())
		}
		accessToken = token.AccessToken
	}

	// ── Fetch user JSON ───────────────────────────────────────────────────────
	req, err := http.NewRequestWithContext(context.Background(), http.MethodGet, userInfoURL, nil)
	if err != nil {
		return userInfo, fmt.Errorf("basic: build userinfo request: %w", err)
	}
	req.Header.Set("Authorization", "Bearer "+accessToken)

	response, err := g.httpClient().Do(req)
	if err != nil {
		return userInfo, fmt.Errorf("failed getting user info: %s", err.Error())
	}
	defer response.Body.Close()
	data, _ := io.ReadAll(response.Body)

	// ── Extract fields via gjson paths ────────────────────────────────────────
	userInfo = plugin.ExternalLoginUserInfo{
		MetaInfo: string(data),
	}
	if len(g.Config.UserIDJsonPath) > 0 {
		userInfo.ExternalID = gjson.GetBytes(data, g.Config.UserIDJsonPath).String()
	}
	if len(userInfo.ExternalID) == 0 {
		log.Errorf("fail to get user id from json path: %s", g.Config.UserIDJsonPath)
		return userInfo, nil
	}
	if len(g.Config.UserDisplayNameJsonPath) > 0 {
		userInfo.DisplayName = gjson.GetBytes(data, g.Config.UserDisplayNameJsonPath).String()
	}
	if len(g.Config.UserUsernameJsonPath) > 0 {
		userInfo.Username = gjson.GetBytes(data, g.Config.UserUsernameJsonPath).String()
	}
	if len(g.Config.UserEmailJsonPath) > 0 {
		userInfo.Email = gjson.GetBytes(data, g.Config.UserEmailJsonPath).String()
	}
	if g.Config.CheckEmailVerified && len(g.Config.EmailVerifiedJsonPath) > 0 {
		if !gjson.GetBytes(data, g.Config.EmailVerifiedJsonPath).Bool() {
			userInfo.Email = ""
		}
	}
	if len(g.Config.UserAvatarJsonPath) > 0 {
		userInfo.Avatar = gjson.GetBytes(data, g.Config.UserAvatarJsonPath).String()
	}

	userInfo = g.formatUserInfo(userInfo)
	return userInfo, nil
}

func (g *Connector) ConfigFields() []plugin.ConfigField {
	fields := make([]plugin.ConfigField, 0)

	// ── Identity ──────────────────────────────────────────────────────────────
	fields = append(fields, createTextInput("name",
		i18n.ConfigNameTitle, i18n.ConfigNameDescription, g.Config.Name, true))

	// ── OIDC auto-discovery ───────────────────────────────────────────────────
	fields = append(fields, createTextInput("issuer_url",
		i18n.ConfigIssuerURLTitle, i18n.ConfigIssuerURLDescription, g.Config.IssuerURL, false))

	// ── OAuth2 credentials ────────────────────────────────────────────────────
	fields = append(fields, createTextInput("client_id",
		i18n.ConfigClientIDTitle, i18n.ConfigClientIDDescription, g.Config.ClientID, true))
	fields = append(fields, createTextInput("client_secret",
		i18n.ConfigClientSecretTitle, i18n.ConfigClientSecretDescription, g.Config.ClientSecret, false))

	// ── Endpoints (optional when issuer_url is set) ───────────────────────────
	fields = append(fields, createTextInput("authorize_url",
		i18n.ConfigAuthorizeUrlTitle, i18n.ConfigAuthorizeUrlDescription, g.Config.AuthorizeUrl, false))
	fields = append(fields, createTextInput("token_url",
		i18n.ConfigTokenUrlTitle, i18n.ConfigTokenUrlDescription, g.Config.TokenUrl, false))
	fields = append(fields, createTextInput("user_json_url",
		i18n.ConfigUserJsonUrlTitle, i18n.ConfigUserJsonUrlDescription, g.Config.UserJsonUrl, false))

	// ── User field mapping ────────────────────────────────────────────────────
	fields = append(fields, createTextInput("user_id_json_path",
		i18n.ConfigUserIDJsonPathTitle, i18n.ConfigUserIDJsonPathDescription, g.Config.UserIDJsonPath, true))
	fields = append(fields, createTextInput("user_display_name_json_path",
		i18n.ConfigUserDisplayNameJsonPathTitle, i18n.ConfigUserDisplayNameJsonPathDescription, g.Config.UserDisplayNameJsonPath, false))
	fields = append(fields, createTextInput("user_username_json_path",
		i18n.ConfigUserUsernameJsonPathTitle, i18n.ConfigUserUsernameJsonPathDescription, g.Config.UserUsernameJsonPath, false))
	fields = append(fields, createTextInput("user_email_json_path",
		i18n.ConfigUserEmailJsonPathTitle, i18n.ConfigUserEmailJsonPathDescription, g.Config.UserEmailJsonPath, false))
	fields = append(fields, createTextInput("user_avatar_json_path",
		i18n.ConfigUserAvatarJsonPathTitle, i18n.ConfigUserAvatarJsonPathDescription, g.Config.UserAvatarJsonPath, false))
	fields = append(fields, plugin.ConfigField{
		Name:  "check_email_verified",
		Type:  plugin.ConfigTypeSwitch,
		Title: plugin.MakeTranslator(i18n.ConfigCheckEmailVerifiedTitle),
		Value: g.Config.CheckEmailVerified,
		UIOptions: plugin.ConfigFieldUIOptions{
			Label: plugin.MakeTranslator(i18n.ConfigCheckEmailVerifiedLabel),
		},
	})
	fields = append(fields, createTextInput("email_verified_json_path",
		i18n.ConfigEmailVerifiedJsonPathTitle, i18n.ConfigEmailVerifiedJsonPathDescription, g.Config.EmailVerifiedJsonPath, false))

	// ── Scope & branding ──────────────────────────────────────────────────────
	fields = append(fields, createTextInput("scope",
		i18n.ConfigScopeTitle, i18n.ConfigScopeDescription, g.Config.Scope, false))
	fields = append(fields, createTextInput("logo_svg",
		i18n.ConfigLogoSVGTitle, i18n.ConfigLogoSVGDescription, g.Config.LogoSVG, false))

	// ── Security ──────────────────────────────────────────────────────────────
	fields = append(fields, plugin.ConfigField{
		Name:        "enable_pkce",
		Type:        plugin.ConfigTypeSwitch,
		Title:       plugin.MakeTranslator(i18n.ConfigEnablePKCETitle),
		Description: plugin.MakeTranslator(i18n.ConfigEnablePKCEDescription),
		Value:       g.Config.EnablePKCE,
	})
	fields = append(fields, plugin.ConfigField{
		Name:        "skip_tls_verify",
		Type:        plugin.ConfigTypeSwitch,
		Title:       plugin.MakeTranslator(i18n.ConfigSkipTLSVerifyTitle),
		Description: plugin.MakeTranslator(i18n.ConfigSkipTLSVerifyDescription),
		Value:       g.Config.SkipTLSVerify,
	})

	return fields
}

func (g *Connector) ConfigReceiver(config []byte) error {
	c := &ConnectorConfig{}
	_ = json.Unmarshal(config, c)
	g.Config = c
	return nil
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

// httpClient returns an HTTP client with a fixed timeout.
// TLS verification is disabled only when the admin has explicitly opted in —
// intended for internal or development identity providers only.
func (g *Connector) httpClient() *http.Client {
	transport := http.DefaultTransport
	if g.Config.SkipTLSVerify {
		transport = &http.Transport{
			TLSClientConfig: &tls.Config{InsecureSkipVerify: true}, //nolint:gosec
		}
	}
	return &http.Client{Transport: transport, Timeout: httpTimeout}
}

// fetchDiscovery retrieves OIDC provider metadata from {issuer}/.well-known/openid-configuration.
func (g *Connector) fetchDiscovery() (*oidcDiscovery, error) {
	issuer := strings.TrimRight(g.Config.IssuerURL, "/")
	discoveryURL := issuer + "/.well-known/openid-configuration"

	req, err := http.NewRequestWithContext(context.Background(), http.MethodGet, discoveryURL, nil)
	if err != nil {
		return nil, err
	}
	resp, err := g.httpClient().Do(req)
	if err != nil {
		return nil, fmt.Errorf("GET %s: %w", discoveryURL, err)
	}
	defer resp.Body.Close()

	if resp.StatusCode != http.StatusOK {
		return nil, fmt.Errorf("discovery endpoint returned HTTP %d", resp.StatusCode)
	}
	var disc oidcDiscovery
	if err := json.NewDecoder(resp.Body).Decode(&disc); err != nil {
		return nil, fmt.Errorf("decode discovery document: %w", err)
	}
	return &disc, nil
}

// resolveEndpoints returns (authURL, tokenURL, userInfoURL).
// When IssuerURL is configured the three URLs come from OIDC discovery.
// Otherwise the manually configured fields are used.
// Manual fields always take precedence over discovered ones.
func (g *Connector) resolveEndpoints() (authURL, tokenURL, userInfoURL string, err error) {
	if g.Config.IssuerURL != "" {
		disc, err := g.fetchDiscovery()
		if err != nil {
			return "", "", "", fmt.Errorf("OIDC discovery failed: %w", err)
		}
		authURL = disc.AuthorizationEndpoint
		tokenURL = disc.TokenEndpoint
		userInfoURL = disc.UserinfoEndpoint
	}
	// Manual fields win when both are provided.
	if g.Config.AuthorizeUrl != "" {
		authURL = g.Config.AuthorizeUrl
	}
	if g.Config.TokenUrl != "" {
		tokenURL = g.Config.TokenUrl
	}
	// user_json_url override is handled in ConnectorReceiver directly.
	return authURL, tokenURL, userInfoURL, nil
}

// exchangeCodeManual performs an RFC 6749 token exchange via a raw HTTP POST,
// including the PKCE code_verifier when provided.
func (g *Connector) exchangeCodeManual(tokenEndpoint, code, verifier, redirectURI string) (*tokenExchangeResponse, error) {
	form := url.Values{
		"grant_type":   {"authorization_code"},
		"code":         {code},
		"redirect_uri": {redirectURI},
		"client_id":    {g.Config.ClientID},
	}
	if g.Config.ClientSecret != "" {
		form.Set("client_secret", g.Config.ClientSecret)
	}
	if verifier != "" {
		form.Set("code_verifier", verifier)
	}

	req, err := http.NewRequestWithContext(context.Background(), http.MethodPost, tokenEndpoint,
		strings.NewReader(form.Encode()))
	if err != nil {
		return nil, err
	}
	req.Header.Set("Content-Type", "application/x-www-form-urlencoded")
	req.Header.Set("Accept", "application/json")

	resp, err := g.httpClient().Do(req)
	if err != nil {
		return nil, err
	}
	defer resp.Body.Close()

	body, _ := io.ReadAll(resp.Body)
	if resp.StatusCode != http.StatusOK {
		return nil, fmt.Errorf("token endpoint returned HTTP %d: %s", resp.StatusCode, body)
	}
	var tokenResp tokenExchangeResponse
	if err := json.Unmarshal(body, &tokenResp); err != nil {
		return nil, fmt.Errorf("decode token response: %w", err)
	}
	return &tokenResp, nil
}

func (g *Connector) formatUserInfo(userInfo plugin.ExternalLoginUserInfo) plugin.ExternalLoginUserInfo {
	if checker.IsInvalidUsername(userInfo.Username) {
		userInfo.Username = replaceUsernameReg.ReplaceAllString(userInfo.Username, "_")
	}
	n := utf8.RuneCountInString(userInfo.Username)
	if n < 4 {
		userInfo.Username += strings.Repeat("_", 4-n)
	} else if n > 30 {
		userInfo.Username = string([]rune(userInfo.Username)[:30])
	}
	return userInfo
}

func createTextInput(name, title, desc, value string, require bool) plugin.ConfigField {
	return plugin.ConfigField{
		Name:        name,
		Type:        plugin.ConfigTypeInput,
		Title:       plugin.MakeTranslator(title),
		Description: plugin.MakeTranslator(desc),
		Required:    require,
		UIOptions: plugin.ConfigFieldUIOptions{
			InputType: plugin.InputTypeText,
		},
		Value: value,
	}
}

// generateCodeVerifier creates a 32-byte cryptographically random PKCE verifier
// encoded as base64url without padding (RFC 7636 §4.1).
func generateCodeVerifier() (string, error) {
	b := make([]byte, 32)
	if _, err := rand.Read(b); err != nil {
		return "", err
	}
	return base64.RawURLEncoding.EncodeToString(b), nil
}

// computeCodeChallenge derives the S256 code challenge from the verifier
// per RFC 7636 §4.2: BASE64URL(SHA256(ASCII(code_verifier))).
func computeCodeChallenge(verifier string) string {
	h := sha256.Sum256([]byte(verifier))
	return base64.RawURLEncoding.EncodeToString(h[:])
}

// randomToken generates n cryptographically random bytes encoded as base64url,
// used for the state parameter.
func randomToken(n int) (string, error) {
	b := make([]byte, n)
	if _, err := rand.Read(b); err != nil {
		return "", err
	}
	return base64.RawURLEncoding.EncodeToString(b), nil
}
