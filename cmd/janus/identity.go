package main

import (
	"bytes"
	"encoding/json"
	"errors"
	"fmt"
	"io/fs"
	"os"
	"path/filepath"
	"strings"
)

const identitySchema = 2

type identityFunc struct {
	Name    string `json:"name"`
	Address string `json:"address"`
	Size    uint64 `json:"size"`
	Words   int    `json:"words"`
	Bytes   int    `json:"bytes,omitempty"` // amd64
}

type identityStub struct {
	Name    string `json:"name"`
	Address string `json:"address"`
	Kind    string `json:"kind"`
}

type identityContract struct {
	Name    string `json:"name"`
	Address string `json:"address"`
}

type identityBranch struct {
	From   string `json:"from"`
	Target string `json:"target"`
}

type identityData struct {
	Name    string `json:"name"`
	Address string `json:"address"`
	Size    int    `json:"size"`
	Section string `json:"section"`
	Sha256  string `json:"sha256"`
}

type identityDataRef struct {
	From   string `json:"from"`
	Target string `json:"target"`
	Kind   string `json:"kind"`
}

type identitySkipped struct {
	From    string `json:"from"`
	Target  string `json:"target"`
	Kind    string `json:"kind"`
	Section string `json:"section"`
	Symbol  string `json:"symbol"`
	Reason  string `json:"reason"`
}

// identityTarget is a function copied because an indirect call may reach it (dynamic.go).
type identityTarget struct {
	Name    string `json:"name"`
	Address string `json:"address"`
	Via     string `json:"via"`            // "targets", "itab", "funcval" or "code-address"
	From    string `json:"from,omitempty"` // the itab/funcval symbol, or the instruction computing the address
}

// identityOmitted is a direct call that is deliberately not followed.
type identityOmitted struct {
	From   string `json:"from"`
	Target string `json:"target"`
	Name   string `json:"name"`
	Reason string `json:"reason"`
}

// Identity is identity.json: what was extracted, from which bytes, by which extractor.
type Identity struct {
	Schema           int            `json:"schema"`
	ExtractorVersion string         `json:"extractorVersion"`
	Binary           string         `json:"binary"`
	BinarySha256     string         `json:"binarySha256"`
	GoVersion        string         `json:"goVersion"`
	MainModule       string         `json:"mainModule"`
	GOOS             string         `json:"goos"`
	GOARCH           string         `json:"goarch"`
	GOAMD64          string         `json:"goamd64,omitempty"`
	SymbolSource     string         `json:"symbolSource"`
	Symbol           string         `json:"symbol"`
	Address          string         `json:"address"`
	Size             uint64         `json:"size"`
	EntryABI         string         `json:"entryABI,omitempty"`    // "ABI0"/"ABIInternal" for Go assembly and ABI wrappers (abi0.go); omitted for Go code
	EntrySource      string         `json:"entrySource,omitempty"` // "assembly" or "abi-wrapper" (informational, docs/ABI0.md)
	MaxFunctions     int            `json:"maxFunctions"`
	Functions        []identityFunc `json:"functions"`
	Stubs            []identityStub `json:"stubs"`
	// ContractPatterns are the --contract patterns of the extraction and Contracts the
	// functions they matched (not followed, recorded in Program.contracts). Both are omitted
	// when empty, so identities written before contracts existed keep their bytes.
	ContractPatterns []string           `json:"contractPatterns,omitempty"`
	Contracts        []identityContract `json:"contracts,omitempty"`
	Unresolved       []identityBranch   `json:"unresolvedBranches"`
	Targets          []string           `json:"targets,omitempty"`
	DynamicTargets   []identityTarget   `json:"dynamicTargets,omitempty"`
	OmittedCalls     []identityOmitted  `json:"omittedCalls,omitempty"`
	Data             []identityData     `json:"data"`
	DataRefs         []identityDataRef  `json:"dataReferences"`
	SkippedData      []identitySkipped  `json:"skippedData"`
	Extracted        string             `json:"extracted"`
	ExtractedSha256  string             `json:"extractedSha256"`
}

func hex0x(v uint64) string { return fmt.Sprintf("0x%x", v) }

// binaryRef records the binary path relative to the artifact directory when possible.
func binaryRef(outdir, binPath string) string {
	absBin, err1 := filepath.Abs(binPath)
	absOut, err2 := filepath.Abs(outdir)
	if err1 != nil || err2 != nil {
		return binPath
	}
	// Relative when both live under the same top-level directory (e.g. one repository
	// checkout), so the artifact directory can move along with the binary.
	top := func(p string) string {
		return strings.SplitN(strings.TrimPrefix(p, string(filepath.Separator)), string(filepath.Separator), 2)[0]
	}
	if top(absBin) == top(absOut) {
		if rel, err := filepath.Rel(absOut, absBin); err == nil {
			return filepath.ToSlash(rel)
		}
	}
	return filepath.ToSlash(absBin)
}

func resolveBinary(outdir, ref string) string {
	p := filepath.FromSlash(ref)
	if filepath.IsAbs(p) {
		return p
	}
	return filepath.Join(outdir, p)
}

func makeIdentity(x *Extraction, binRef string, maxFunctions int) *Identity {
	id := &Identity{
		Schema:           identitySchema,
		ExtractorVersion: extractorVersion,
		Binary:           binRef,
		BinarySha256:     x.Bin.Sha256,
		GoVersion:        x.Bin.GoVersion,
		MainModule:       x.Bin.MainModule,
		GOOS:             x.Bin.GOOS,
		GOARCH:           x.Bin.GOARCH,
		GOAMD64:          x.Bin.GOAMD64,
		SymbolSource:     x.Bin.SymbolSource,
		Symbol:           x.Entry.Name,
		Address:          hex0x(x.Entry.Addr),
		Size:             x.Entry.Size,
		MaxFunctions:     maxFunctions,
		Functions:        []identityFunc{},
		Stubs:            []identityStub{},
		Unresolved:       []identityBranch{},
		Data:             []identityData{},
		DataRefs:         []identityDataRef{},
		SkippedData:      []identitySkipped{},
		Extracted:        "Extracted.lean",
		ExtractedSha256:  sha256Hex(x.Lean),
	}
	id.EntryABI, id.EntrySource = entryABI(x.Bin, x.Entry)
	for _, s := range x.Segments {
		id.Functions = append(id.Functions, identityFunc{s.Name, hex0x(s.Base), s.Size, len(s.Words), len(s.Bytes)})
	}
	for _, s := range x.Stubs {
		id.Stubs = append(id.Stubs, identityStub{s.Name, hex0x(s.Addr), string(s.Kind)})
	}
	id.ContractPatterns = append([]string(nil), x.ContractPatterns...)
	for _, c := range x.Contracts {
		id.Contracts = append(id.Contracts, identityContract{c.Name, hex0x(c.Addr)})
	}
	for _, u := range x.Unresolved {
		id.Unresolved = append(id.Unresolved, identityBranch{hex0x(u.From), hex0x(u.Target)})
	}
	id.Targets = append(id.Targets, x.Targets...)
	for _, t := range x.Dynamic {
		id.DynamicTargets = append(id.DynamicTargets, identityTarget{t.Name, hex0x(t.Addr), t.Via, t.From})
	}
	for _, o := range x.Omitted {
		id.OmittedCalls = append(id.OmittedCalls, identityOmitted{hex0x(o.From), hex0x(o.Target), o.Name, o.Reason})
	}
	for _, d := range x.Data {
		id.Data = append(id.Data, identityData{d.Name, hex0x(d.Base), len(d.Bytes), d.Section, sha256Hex(d.Bytes)})
	}
	for _, r := range x.DataRefs {
		id.DataRefs = append(id.DataRefs, identityDataRef{hex0x(r.From), hex0x(r.Target), r.Kind})
	}
	for _, s := range x.Skipped {
		id.SkippedData = append(id.SkippedData, identitySkipped{hex0x(s.From), hex0x(s.Target), s.Kind, s.Section, s.Symbol, s.Reason})
	}
	return id
}

// contractList renders the recorded contracts as "name @ address".
func (id *Identity) contractList() []string {
	var out []string
	for _, c := range id.Contracts {
		out = append(out, c.Name+" @ "+c.Address)
	}
	return out
}

func (id *Identity) marshal() []byte {
	b, err := json.MarshalIndent(id, "", "  ")
	if err != nil {
		panic(err)
	}
	return append(b, '\n')
}

func writeArtifacts(outdir string, x *Extraction, id *Identity) error {
	if err := os.MkdirAll(outdir, 0o755); err != nil {
		return err
	}
	// A new extraction invalidates any earlier verification of this directory.
	_ = os.Remove(filepath.Join(outdir, "verified.json"))
	if err := os.WriteFile(filepath.Join(outdir, "Extracted.lean"), x.Lean, 0o644); err != nil {
		return err
	}
	return os.WriteFile(filepath.Join(outdir, "identity.json"), id.marshal(), 0o644)
}

// CheckResult is what a successful check established.
type CheckResult struct {
	Outdir    string
	Identity  *Identity
	BinPath   string
	Lean      []byte // the saved (and regenerated) Extracted.lean
	Extracted string // path of Extracted.lean
}

func rerunExtract(id *Identity, outdir string) string {
	if id == nil || id.Symbol == "" {
		return "Rerun janus extract <binary> <symbol> " + outdir + ", then rerun this command."
	}
	targets := ""
	if len(id.Targets) > 0 {
		targets = fmt.Sprintf(" --targets %q", strings.Join(id.Targets, ","))
	}
	return fmt.Sprintf("Rerun janus extract %s %q %s%s with the intended binary, then rerun this command.",
		displayPath(resolveBinary(outdir, id.Binary)), id.Symbol, displayPath(outdir), targets)
}

// check regenerates the extraction recorded in outdir/identity.json and compares it with
// the saved files. binOverride, if set, replaces the recorded binary path (content must match).
func check(outdir, binOverride string) (*CheckResult, error) {
	idPath := filepath.Join(outdir, "identity.json")
	raw, err := os.ReadFile(idPath)
	if err != nil {
		msg := fmt.Sprintf("Cannot read %s: %v", displayPath(idPath), err)
		if errors.Is(err, fs.ErrNotExist) {
			msg = fmt.Sprintf("%s does not exist; %s is not an extraction directory.", displayPath(idPath), displayPath(outdir))
		}
		return nil, &diag{Invalid: true, Msg: msg, Stage: "artifact layout", Next: rerunExtract(nil, outdir)}
	}
	var id Identity
	dec := json.NewDecoder(bytes.NewReader(raw))
	dec.DisallowUnknownFields()
	if err := dec.Decode(&id); err != nil {
		return nil, &diag{Invalid: true, Msg: fmt.Sprintf("%s is malformed: %v", displayPath(idPath), err),
			Stage: "artifact layout", Next: rerunExtract(nil, outdir)}
	}
	if id.Schema != identitySchema || id.ExtractorVersion != extractorVersion {
		return nil, &diag{Invalid: true,
			Msg: fmt.Sprintf("%s was written by extractor %s (schema %d); this is janus %s (schema %d).",
				displayPath(idPath), id.ExtractorVersion, id.Schema, extractorVersion, identitySchema),
			Stage: "extractor version", Next: rerunExtract(&id, outdir)}
	}
	if id.Extracted != "Extracted.lean" {
		return nil, &diag{Invalid: true, Msg: fmt.Sprintf("%s names an unexpected extraction file %q.", displayPath(idPath), id.Extracted),
			Stage: "artifact layout", Next: rerunExtract(&id, outdir)}
	}

	binPath := resolveBinary(outdir, id.Binary)
	if binOverride != "" {
		binPath = binOverride
	}
	b, err := loadBinary(binPath)
	if err != nil {
		d := err.(*diag)
		d.Invalid = true
		if binOverride == "" {
			d.Next = "If the binary moved, pass --binary path/to/binary (its SHA-256 must still match identity.json). " +
				rerunExtract(&id, outdir)
		}
		return nil, d
	}
	if b.Sha256 != id.BinarySha256 {
		return nil, &diag{Invalid: true,
			Msg: fmt.Sprintf("Binary changed since extraction: %s has SHA-256 %s, identity.json records %s.",
				displayPath(binPath), b.Sha256, id.BinarySha256),
			Stage: "binary identity", Next: rerunExtract(&id, outdir)}
	}

	leanPath := filepath.Join(outdir, "Extracted.lean")
	saved, err := os.ReadFile(leanPath)
	if err != nil {
		return nil, &diag{Invalid: true, Msg: fmt.Sprintf("Cannot read %s: %v", displayPath(leanPath), err),
			Stage: "artifact layout", Next: rerunExtract(&id, outdir)}
	}
	if got := sha256Hex(saved); got != id.ExtractedSha256 {
		return nil, &diag{Invalid: true,
			Msg: fmt.Sprintf("%s was modified after extraction: SHA-256 %s, identity.json records %s.",
				displayPath(leanPath), got, id.ExtractedSha256),
			Stage: "extraction integrity", Next: rerunExtract(&id, outdir)}
	}

	x, err := extractWith(b, id.Symbol, id.MaxFunctions, id.ContractPatterns, id.Targets...)
	if err != nil {
		d := err.(*diag)
		d.Invalid = true
		return nil, d
	}
	if !bytes.Equal(x.Lean, saved) {
		return nil, &diag{Invalid: true,
			Msg: fmt.Sprintf("Stale or mismatched artifact: %s differs from the regenerated extraction (%s).",
				displayPath(leanPath), firstDiff(saved, x.Lean)),
			Stage: "extraction integrity", Next: rerunExtract(&id, outdir)}
	}
	regen := makeIdentity(x, id.Binary, id.MaxFunctions)
	if !bytes.Equal(regen.marshal(), (&id).marshal()) {
		return nil, &diag{Invalid: true,
			Msg:   fmt.Sprintf("Stale or mismatched artifact: %s differs from the regenerated identity.", displayPath(idPath)),
			Stage: "extraction integrity", Next: rerunExtract(&id, outdir)}
	}
	return &CheckResult{Outdir: outdir, Identity: &id, BinPath: binPath, Lean: saved, Extracted: leanPath}, nil
}

func firstDiff(a, b []byte) string {
	al := strings.Split(string(a), "\n")
	bl := strings.Split(string(b), "\n")
	for i := 0; i < len(al) || i < len(bl); i++ {
		var x, y string
		if i < len(al) {
			x = al[i]
		}
		if i < len(bl) {
			y = bl[i]
		}
		if x != y {
			return fmt.Sprintf("first difference at line %d", i+1)
		}
	}
	return "files differ"
}
