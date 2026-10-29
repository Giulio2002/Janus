// Package janus carries the Janus Lean framework sources, so that the janus command
// (github.com/Giulio2002/Janus/cmd/janus) can verify proofs without a checkout of this
// repository: `go install github.com/Giulio2002/Janus/cmd/janus@latest` is enough.
//
// The bundled framework is exactly these files, as they were when the binary was built.
// janus verify builds them (once, in a local cache) and checks that a consumer package's
// janus dependency has the same sources. See docs/CLI.md and docs/CONSUMERS.md.
package janus

import "embed"

// Framework holds the Lean library (Janus.lean and every file under Janus/), its Lake
// configuration and manifest, and the pinned Lean toolchain.
//
//go:embed Janus.lean Janus lakefile.toml lake-manifest.json lean-toolchain
var Framework embed.FS

// ASL holds the JanusASL Lake package (docs/ASL.md): its configuration, its Lean sources and the
// vendored, generated ArmASL model (vendor/ArmASL.tar.gz, with its SHA-256 and version pins).
// `janus verify --asl` builds it once per framework and JanusASL version in the local cache.
//
//go:embed JanusASL/lakefile.toml JanusASL/lake-manifest.json JanusASL/lean-toolchain JanusASL/JanusASL JanusASL/vendor
var ASL embed.FS

// GoSources holds the Go source of the janus command and of this package (every .go file of the
// repository root and of cmd/janus, test files included: consumers skip them) together with go.mod
// and go.sum. janus hashes it (cmd/janus/verifierid.go) to identify the exact verifier source it
// was built from, which keys its verification-result cache independently of the checkout and
// directory it was built in (docs/SOUNDNESS.md, "Result-cache verifier identity"). A new Go
// package imported by cmd/janus from this module must be added here; a test enforces that.
//
// Every file of cmd/janus is embedded (not only *.go): assembly files (.s), headers they include and
// .syso objects are compiled with cgo disabled too, and an edit of one is an edit of the verifier. The
// root package has only Go source; identity_sentinel.s/.h make the patterns for its assembly files and
// headers match, so that adding one is embedded (and hashed) rather than silently ignored.
//
//go:embed go.mod go.sum *.go *.s *.h cmd/janus
var GoSources embed.FS
