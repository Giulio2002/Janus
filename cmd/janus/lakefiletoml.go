package main

import (
	"path"
	"strings"
)

// Cacheability of a Lake configuration for the verification-result cache (resultcache.go).
//
// The cache key covers the package snapshot and the pinned dependencies. A Lake configuration
// that makes Lake or Lean read anything else (a source directory outside the package, plugin or
// link arguments, arbitrary code in a lakefile.lean) is not covered, so such packages are never
// cached. The decision is made on a strictly parsed subset of TOML, fail closed: the parser
// accepts only the constructs below, in exactly the forms below, and anything else (a quoted or
// dotted key, an inline table, a multi-line string, an escape, a carriage return, a table not in
// the whitelist…) makes the configuration non-cacheable. It does not try to be a TOML parser; it
// only has to accept a plain lakefile and to understand what it accepts exactly as Lake does.
//
//	file      = { blank | comment | header | pair }
//	header    = "[[" name "]]" | "[" name "]"            name in lakefileTomlTables
//	pair      = barekey "=" value                         barekey = [A-Za-z0-9_-]+ (in [leanOptions]: [A-Za-z0-9_.-]+)
//	value     = "basic string without \" | 'literal string' | integer | true | false | array
//	array     = "[" [ value { "," value } [","] ] "]"     (may span lines, comments allowed)
//
// A pair or header is followed only by spaces, an optional comment and the end of the line.

var lakefileTomlTables = map[string]bool{
	"require": true, "lean_lib": true, "lean_exe": true, "leanOptions": true,
}

// lakefileTomlKeys are the keys accepted outside [leanOptions]: none of them reads a file outside
// the package snapshot or changes what Lean loads. `srcDir` is accepted only when it stays inside
// the package; `path` is a path dependency, which loadConsumer admits only with
// --allow-path-deps and the key covers by its tree hash.
var lakefileTomlKeys = map[string]bool{
	"name": true, "defaultTargets": true, "version": true, "versionTags": true, "description": true,
	"keywords": true, "homepage": true, "license": true, "licenseFiles": true, "readmeFile": true,
	"reservoir": true, "roots": true, "globs": true, "libName": true, "srcDir": true, "root": true,
	"exeName": true, "supportInterpreter": true, "buildType": true, "precompileModules": true,
	"platformIndependent": true, "scope": true, "git": true, "rev": true, "subDir": true,
	"path": true, "inputRev": true, "type": true, "dir": true,
}

type tomlPair struct {
	table string // "" at the top level, else the table name
	key   string
	str   string   // the decoded value when it is a string
	isStr bool     // the value is a string
	strs  []string // every string of the value (the string itself, or the strings of an array)
}

type tomlScanner struct {
	s    string
	i    int
	bad  bool
	strs []string // strings scanned since the last reset
}

func (t *tomlScanner) fail() { t.bad = true }

func (t *tomlScanner) peek() byte {
	if t.i < len(t.s) {
		return t.s[t.i]
	}
	return 0
}

func (t *tomlScanner) skipSpaces() {
	for t.i < len(t.s) && (t.s[t.i] == ' ' || t.s[t.i] == '\t') {
		t.i++
	}
}

// skipComment consumes "# …" up to (not including) the newline.
func (t *tomlScanner) skipComment() {
	if t.peek() == '#' {
		for t.i < len(t.s) && t.s[t.i] != '\n' {
			t.i++
		}
	}
}

// endOfLine: only spaces and a comment may precede the newline (or the end of the file).
func (t *tomlScanner) endOfLine() {
	t.skipSpaces()
	t.skipComment()
	if t.i < len(t.s) {
		if t.s[t.i] != '\n' {
			t.fail()
			return
		}
		t.i++
	}
}

func isBareKeyByte(c byte, dots bool) bool {
	return c >= 'a' && c <= 'z' || c >= 'A' && c <= 'Z' || c >= '0' && c <= '9' || c == '_' || c == '-' || dots && c == '.'
}

func (t *tomlScanner) bareKey(dots bool) string {
	start := t.i
	for t.i < len(t.s) && isBareKeyByte(t.s[t.i], dots) {
		t.i++
	}
	if t.i == start {
		t.fail()
	}
	return t.s[start:t.i]
}

// value scans one value; for a string it returns its decoded text.
func (t *tomlScanner) value() (str string, isStr bool) {
	switch c := t.peek(); {
	case c == '"':
		if strings.HasPrefix(t.s[t.i:], `"""`) {
			t.fail()
			return
		}
		t.i++
		start := t.i
		for t.i < len(t.s) && t.s[t.i] != '"' {
			if t.s[t.i] == '\\' || t.s[t.i] == '\n' {
				t.fail() // no escapes, no line breaks: what is read is what is meant
				return
			}
			t.i++
		}
		if t.i >= len(t.s) {
			t.fail()
			return
		}
		str = t.s[start:t.i]
		t.i++
		t.strs = append(t.strs, str)
		return str, true
	case c == '\'':
		if strings.HasPrefix(t.s[t.i:], `'''`) {
			t.fail()
			return
		}
		t.i++
		start := t.i
		for t.i < len(t.s) && t.s[t.i] != '\'' {
			if t.s[t.i] == '\n' {
				t.fail()
				return
			}
			t.i++
		}
		if t.i >= len(t.s) {
			t.fail()
			return
		}
		str = t.s[start:t.i]
		t.i++
		t.strs = append(t.strs, str)
		return str, true
	case c == '[':
		t.i++
		for {
			t.skipArrayGap()
			if t.bad {
				return
			}
			if t.peek() == ']' {
				t.i++
				return "", false
			}
			t.value()
			if t.bad {
				return
			}
			t.skipArrayGap()
			switch t.peek() {
			case ',':
				t.i++
			case ']':
			default:
				t.fail()
				return
			}
		}
	case c == 't' && strings.HasPrefix(t.s[t.i:], "true"):
		t.i += 4
	case c == 'f' && strings.HasPrefix(t.s[t.i:], "false"):
		t.i += 5
	case c >= '0' && c <= '9' || c == '-' || c == '+':
		t.i++
		for t.i < len(t.s) && (t.s[t.i] >= '0' && t.s[t.i] <= '9' || t.s[t.i] == '_') {
			t.i++
		}
	default: // inline tables, floats with exponents, dates, anything else
		t.fail()
	}
	return
}

// skipArrayGap skips spaces, newlines and comments between array elements.
func (t *tomlScanner) skipArrayGap() {
	for t.i < len(t.s) {
		switch t.s[t.i] {
		case ' ', '\t', '\n':
			t.i++
		case '#':
			t.skipComment()
		default:
			return
		}
	}
}

// parseLakefileToml decodes src, or reports false if it is outside the accepted subset.
func parseLakefileToml(src string) ([]tomlPair, bool) {
	for i := 0; i < len(src); i++ {
		if c := src[i]; c == '\r' || c == 0 || c < 0x20 && c != '\n' && c != '\t' || c == 0x7f {
			return nil, false
		}
	}
	t := &tomlScanner{s: src}
	var out []tomlPair
	table := ""
	for t.i < len(t.s) && !t.bad {
		t.skipSpaces()
		switch t.peek() {
		case '\n':
			t.i++
		case '#':
			t.skipComment()
		case '[':
			double := strings.HasPrefix(t.s[t.i:], "[[")
			if double {
				t.i += 2
			} else {
				t.i++
			}
			t.skipSpaces()
			name := t.bareKey(false)
			t.skipSpaces()
			closing := "]"
			if double {
				closing = "]]"
			}
			if !strings.HasPrefix(t.s[t.i:], closing) || !lakefileTomlTables[name] || (name == "leanOptions") == double {
				t.fail()
				break
			}
			t.i += len(closing)
			table = name
			t.endOfLine()
		default:
			key := t.bareKey(table == "leanOptions")
			t.skipSpaces()
			if t.peek() != '=' {
				t.fail()
				break
			}
			t.i++
			t.skipSpaces()
			t.strs = nil
			str, isStr := t.value()
			if t.bad {
				break
			}
			out = append(out, tomlPair{table: table, key: key, str: str, isStr: isStr, strs: t.strs})
			t.endOfLine()
		}
	}
	return out, !t.bad
}

// srcDirInside: v names a relative directory that stays inside the package.
func srcDirInside(v string) bool {
	if v == "" || strings.HasPrefix(v, "/") || strings.HasPrefix(v, "~") || strings.ContainsAny(v, "\\\x00:") {
		return false
	}
	for _, c := range strings.Split(v, "/") {
		// the snapshot skips dot directories and skippedDirs, while the workspace keeps .lake across runs and a
		// sandboxed build can write there: sources below them are not covered by the cache key (round 15a)
		if c == ".." || (strings.HasPrefix(c, ".") && c != ".") || skippedDirs[c] {
			return false
		}
	}
	return path.Clean(v) != ".." && !strings.HasPrefix(path.Clean(v), "../")
}

// lakefileCacheable: whether the result cache may answer for a package (or dependency) with this
// Lake configuration (see the comment at the top of this file).
func lakefileCacheable(files map[string][]byte, config string) bool {
	if config != "lakefile.toml" {
		return false
	}
	src, ok := files[config]
	if !ok {
		return false
	}
	pairs, ok := parseLakefileToml(string(src))
	if !ok {
		return false
	}
	for _, p := range pairs {
		if p.table == "leanOptions" {
			if !leanOptionOK(p.key) { // option names only from a whitelist; the values are plain scalars
				return false
			}
			continue
		}
		if !lakefileTomlKeys[p.key] {
			return false
		}
		if p.key == "srcDir" && (!p.isStr || !srcDirInside(p.str)) {
			return false
		}
		if moduleNameKeys[p.key] {
			for _, v := range p.strs {
				if !plainModuleName(v) {
					return false
				}
			}
		}
	}
	return true
}

// moduleNameKeys hold module/library/target names (or globs of module names): Lake resolves them
// below srcDir, and a name that contains a path separator, `..` or a quoted-identifier marker can
// resolve elsewhere (`roots = ["«..».«..».X"]`).
var moduleNameKeys = map[string]bool{
	"roots": true, "globs": true, "name": true, "libName": true, "root": true, "exeName": true,
	"defaultTargets": true,
}

func plainModuleName(v string) bool {
	if v == "" || strings.Contains(v, "..") || strings.ContainsAny(v, "/\\«»\x00:") {
		return false
	}
	// a module `a.b.C` is the file a/b/C.lean below srcDir: no empty component and none of the directories the
	// snapshot skips (round 15a), so every file a root can name is a file of the snapshot
	for _, c := range strings.Split(v, ".") {
		if c == "" && !strings.Contains(v, "*") && !strings.Contains(v, "+") {
			return false
		}
		if skippedDirs[c] {
			return false
		}
	}
	return true
}

// leanOptionOK: the option names a package may set in [leanOptions] and still be cached. Options
// that make Lean load code or write files (plugins, trace outputs, debug.*) are not among them.
func leanOptionOK(name string) bool {
	name = strings.TrimPrefix(name, "weak.")
	for _, p := range []string{"pp.", "linter."} {
		if strings.HasPrefix(name, p) {
			return true
		}
	}
	switch name {
	case "maxHeartbeats", "maxRecDepth", "autoImplicit", "relaxedAutoImplicit", "synthInstance.maxHeartbeats",
		"synthInstance.maxSize", "exponentiation.threshold", "tactic.hygienic", "Elab.async", "warningAsError":
		return true
	}
	return false
}
