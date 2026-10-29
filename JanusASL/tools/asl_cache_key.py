#!/usr/bin/env python3
"""The key of the shared ArmASL build cache (scripts/asl.sh, ASL_CACHE; docs/ASL.md "Build cache").

    python3 -I JanusASL/tools/asl_cache_key.py REPO_ROOT          the key (32 hex digits)
    python3 -I JanusASL/tools/asl_cache_key.py REPO_ROOT --show   the canonical inputs it hashes

A cache entry holds the ArmASL build outputs (oleans, ileans, C, objects, Lake traces) and the
lean-sail package. The key is the SHA-256 of exactly the inputs those outputs are a function of,
which is a superset of what Lake 4.34 itself hashes into each ArmASL module's trace
(Lake/Build/Module.lean, `recFetchPreSetup`; see the trace files in the entry) plus the inputs
Lake does not trace but that still reach the outputs (weak arguments, leanc arguments):

  * the vendored model tarball (its SHA-256 file, checked against the tarball by `unpack`): the
    sources of every ArmASL module;
  * the splitter (split_lean.py), as before (it only runs in `gen`, so this is conservative);
  * both lean-toolchain files (JanusASL's is the one elan runs in JanusASL/; the root's is the
    framework's);
  * the lean-sail entry of JanusASL/lake-manifest.json (url, rev, ...) and the manifest's
    packagesDir: the only package ArmASL imports, and where it lives;
  * JanusASL/lakefile.toml, parsed and reduced to
      - every package-level setting except the ones listed in PKG_IGNORED below (an unknown or
        new setting is therefore keyed: the default is to key, not to drop),
      - every lean_lib / lean_exe table that can own an ArmASL module: the ArmASL lib itself and
        any target whose name, roots, globs or root is ArmASL or ArmASL.* (Lake builds a module
        with the options of the first library that claims it), in file order;
  * the package-level extraDepTargets of the janus package (`path = ".."`): Lake mixes the
    transitive dependencies' extraDepTargets into every module trace;
  * the content of the toolchain `lean` resolves to in JanusASL/ (driver binaries, libleanshared and
    every core .olean, by SHA-256; `lean --version`), the environment variables that reach the
    compilers (ENV_KEYS) and the machine architecture;
  * the version of this key scheme (SCHEME).

What is left out, and why it cannot change the ArmASL outputs:

  * the [[require]] tables: Lake builds from the manifest (keyed above); `janus` is not imported
    by any ArmASL module (they import only Sail and ArmASL.*);
  * every lean_lib / lean_exe that cannot own an ArmASL module (JanusASL, janus-asl-check, any
    new one): a target's options apply only to its own modules, and the modules it imports are
    built with their own library's options;
  * the PKG_IGNORED settings: metadata, default targets/scripts, drivers, release/Reservoir and
    server-only settings; none of them reaches a `lean` or `leanc` command line or a module trace;
  * comments and formatting of the lakefile (it is parsed, and the result is serialised canonically);
  * the janus package's sources and lakefile otherwise (no ArmASL module imports it).

If JanusASL has a lakefile.lean, or Python has no tomllib, the whole configuration file is hashed
instead (conservative: any change is a miss).
"""
import hashlib
import json
import os
import platform
import sys

SCHEME = "armasl-cache-key-v3"

# Package-level settings that cannot reach a lean/leanc command line or a module trace.
PKG_IGNORED = {
    "version", "versionTags", "description", "keywords", "homepage", "license", "licenseFiles",
    "readmeFile", "reservoir", "defaultTargets", "defaultScripts", "testDriver", "testDriverArgs",
    "lintDriver", "lintDriverArgs", "releaseRepo", "buildArchive", "preferReleaseBuild",
    "moreGlobalServerArgs", "moreServerOptions", "fixedToolchain",
    # target tables, handled separately
    "require", "lean_lib", "lean_exe",
}

MODEL = "ArmASL"

# Environment variables that can reach lean, leanc, lake or the C compiler they run. They are keyed
# by value (an unset variable is absent), so a build under another compiler or flags is another key.
ENV_KEYS = ["LEAN_CC", "LEAN_CXX", "LEAN_SYSROOT", "LEAN_PATH", "LEAN_SRC_PATH", "LEAN_ABORT_ON_PANIC",
            "LAKE_HOME", "LAKE_OVERRIDE_LEAN", "LAKE_NO_CACHE", "ELAN_TOOLCHAIN", "CC", "CXX", "CFLAGS",
            "CXXFLAGS", "CPPFLAGS", "LDFLAGS", "LIBRARY_PATH", "C_INCLUDE_PATH", "CPATH"]


ENV_PREFIXES = ("LEAN_", "LAKE_", "ELAN_", "LD_", "LC_", "GIT_")  # every variable of these families is keyed
ENV_KEYS += ["LANG", "LANGUAGE", "PKG_CONFIG_PATH", "SDKROOT", "TMPDIR_NOT_KEYED"]
ENV_KEYS.remove("TMPDIR_NOT_KEYED")


def env_inputs():
    return {k: v for k, v in sorted(os.environ.items()) if k in ENV_KEYS or k.startswith(ENV_PREFIXES)}


def exe_sha(name):
    """SHA-256 of the executable `name` resolves to on PATH (by content, through symlinks), 'missing' if none."""
    import shutil
    p = shutil.which(name)
    if not p:
        return "missing"
    try:
        return sha(read(os.path.realpath(p)))
    except OSError:
        return "unreadable"


_TC_MEMO = {}


def toolchain_content(cwd):
    if cwd not in _TC_MEMO:
        _TC_MEMO[cwd] = _toolchain_content(cwd)
    return _TC_MEMO[cwd]


def _toolchain_content(cwd):
    """What the toolchain that `lean` resolves to in cwd (elan) consists of, by content: the SHA-256 of
    its driver binaries and of every core .olean (Init, Std, Lean, Lake), plus `lean --version`.
    Lake additionally checks every import's content through its traces; this closes the other
    direction (a swapped compiler or core library under an unchanged lean-toolchain name)."""
    import subprocess
    try:
        ver = subprocess.run(["lean", "--version"], cwd=cwd, capture_output=True, text=True, timeout=120).stdout.strip()
        prefix = subprocess.run(["lean", "--print-prefix"], cwd=cwd, capture_output=True, text=True, timeout=120).stdout.strip()
    except Exception:
        return {"unavailable": True}
    out = {"version": ver}
    if not prefix or not os.path.isdir(prefix):
        out["prefix"] = "missing"
        return out
    h = hashlib.sha256()
    n = 0
    files = []
    # every driver binary (lean, lake, leanc, leanchecker, clang, ld.lld, llvm-ar, cadical, leantar, ...)
    bindir = os.path.join(prefix, "bin")
    files += [os.path.join(bindir, f) for f in sorted(os.listdir(bindir))] if os.path.isdir(bindir) else []
    # the native libraries and objects Lean programs link against, and the C headers they compile against
    for sub in ("lib", "lib/lean"):
        d = os.path.join(prefix, sub)
        files += [os.path.join(d, f) for f in sorted(os.listdir(d))
                  if os.path.isfile(os.path.join(d, f)) and (f.endswith((".a", ".o", ".so", ".dylib")) or ".so." in f)] if os.path.isdir(d) else []
    for top in ("include", "lib/lean"):
        for d, dirs, fs in os.walk(os.path.join(prefix, top)):
            dirs.sort()
            files += [os.path.join(d, f) for f in sorted(fs) if (top == "include" and f.endswith((".h", ".hpp"))) or
                      (top == "lib/lean" and f.endswith((".olean", ".ilean")))]
    for f in files:
        try:
            h.update(os.path.relpath(f, prefix).encode() + b"\0" + sha(read(os.path.realpath(f))).encode() + b"\0")
            n += 1
        except OSError:
            h.update(os.path.relpath(f, prefix).encode() + b"\0missing\0")
    # tools outside the toolchain that lake or leanc may run (a git clone of a package, the system cc/ld)
    out["system"] = {t: exe_sha(os.environ.get(t.upper()) or t) for t in ("cc", "ld", "git")}
    out["files"] = n
    out["sha256"] = h.hexdigest()
    return out


def claims_model(value):
    """Whether a name/roots/globs/root value can denote an ArmASL module."""
    if isinstance(value, str):
        return value == MODEL or value.startswith(MODEL + ".")
    if isinstance(value, list):
        return any(claims_model(v) for v in value)
    if isinstance(value, dict):
        return any(claims_model(v) for v in value.values())
    return False


def read(path):
    with open(path, "rb") as f:
        return f.read()


def sha(data):
    return hashlib.sha256(data).hexdigest()


def inputs(root):
    pkg = os.path.join(root, "JanusASL")
    out = {
        "scheme": SCHEME,
        "model": read(os.path.join(pkg, "vendor", "ArmASL.tar.gz.sha256")).decode().split()[0],
        "splitter": sha(read(os.path.join(pkg, "sail", "split_lean.py"))),
        "toolchain": read(os.path.join(root, "lean-toolchain")).decode().strip(),
        "toolchain.JanusASL": read(os.path.join(pkg, "lean-toolchain")).decode().strip(),
        "toolchain.content": toolchain_content(pkg),
        "env": env_inputs(),
        "machine": platform.machine(),
    }
    manifest = json.loads(read(os.path.join(pkg, "lake-manifest.json")))
    out["manifest.packagesDir"] = manifest.get("packagesDir")
    sail = [p for p in manifest.get("packages", []) if p.get("name") == "Sail"]
    if len(sail) != 1:
        sys.exit("asl_cache_key: JanusASL/lake-manifest.json has %d Sail entries" % len(sail))
    out["manifest.Sail"] = sail[0]

    try:
        import tomllib
    except ImportError:
        tomllib = None
    lean_cfg = os.path.join(pkg, "lakefile.lean")
    toml_cfg = os.path.join(pkg, "lakefile.toml")
    if tomllib is None or os.path.exists(lean_cfg) or not os.path.exists(toml_cfg):
        cfg = lean_cfg if os.path.exists(lean_cfg) else toml_cfg
        out["lakefile.whole"] = sha(read(cfg))
    else:
        cfg = tomllib.loads(read(toml_cfg).decode())
        out["lakefile.package"] = {k: v for k, v in cfg.items() if k not in PKG_IGNORED}
        owners = []
        for kind in ("lean_lib", "lean_exe"):
            for t in cfg.get(kind, []):
                if any(claims_model(t.get(k)) for k in ("name", "roots", "globs", "root")):
                    owners.append({"kind": kind, "config": t})
        if not any(o["kind"] == "lean_lib" and o["config"].get("name") == MODEL for o in owners):
            sys.exit("asl_cache_key: JanusASL/lakefile.toml has no lean_lib %s" % MODEL)
        # Lake resolves a module to the first target that claims it: keep the file order.
        out["lakefile.owners"] = owners

    janus_toml = os.path.join(root, "lakefile.toml")
    if tomllib is not None and os.path.exists(janus_toml) and not os.path.exists(os.path.join(root, "lakefile.lean")):
        out["janus.extraDepTargets"] = tomllib.loads(read(janus_toml).decode()).get("extraDepTargets", [])
    else:
        out["janus.lakefile.whole"] = sha(read(os.path.join(
            root, "lakefile.lean" if os.path.exists(os.path.join(root, "lakefile.lean")) else "lakefile.toml")))
    return out


def canonical(obj):
    return json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=True)


def main():
    if len(sys.argv) < 2:
        sys.exit(__doc__)
    obj = inputs(sys.argv[1])
    if "--show" in sys.argv[2:]:
        print(json.dumps(obj, sort_keys=True, indent=1))
    else:
        print(sha(canonical(obj).encode())[:32])


if __name__ == "__main__":
    main()
