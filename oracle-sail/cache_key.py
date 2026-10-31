#!/usr/bin/env python3
"""The key of the Sail oracle driver's build cache (scripts/oracle-sail.sh; docs/SOUNDNESS.md
"Build caches").

    python3 -I oracle-sail/cache_key.py ROOT --pins K=V ... [--model-file F] [--show]

The driver `oracle-sail/target/release/janus-oracle-sail` is a function of exactly:

  * the pinned crate revision and the SHA-256 of its vendored model (the script's pins, passed in
    --pins together with the cargo flags and the model flavour): the Sail-generated C++ the driver
    embeds; for SAIL_MODEL=regen the SHA-256 of the regenerated model.cpp itself (--model-file);
  * instrument_model.py, which rewrites that model before it is compiled, and (SAIL_SPLIT=1, the default)
    split_model.py / split_crate.py / build.rs.patch (and dir_digest.py, the integrity records of the model directories), which cut it into the translation units that are compiled;
  * oracle-sail/Cargo.toml, Cargo.lock (every dependency version and checksum), src/**, build.rs,
    rust-toolchain files and every .cargo/config file cargo reads;
  * rustc -vV and cargo -V, the C++ compiler (`$CXX`, else c++) --version, and the SHA-256 of the
    system libgmp the driver links dynamically;
  * the environment variables that reach cargo, rustc or the C++ compiler (CARGO_*, RUSTC*,
    RUSTFLAGS, CC/CXX/CFLAGS/CXXFLAGS/CPPFLAGS/LDFLAGS and their per-target forms);
  * the machine architecture and the version of this scheme.
"""
import hashlib
import json
import os
import platform
import subprocess
import sys

SCHEME = "oracle-sail-driver-key-v1"
ENV_PREFIXES = ("CARGO_", "RUSTC", "RUSTUP_", "RUSTFLAGS", "RUSTDOC", "CC_", "CXX_", "CFLAGS_", "CXXFLAGS_", "CPPFLAGS_",
                "LDFLAGS_", "TARGET_", "HOST_", "AARCH64_ORACLE")
ENV_NAMES = ("CC", "CXX", "CFLAGS", "CXXFLAGS", "CPPFLAGS", "LDFLAGS", "AR", "LD", "LIBRARY_PATH",
             "C_INCLUDE_PATH", "CPLUS_INCLUDE_PATH", "CPATH", "PKG_CONFIG_PATH", "GMP_LIB_DIR", "GMP_INCLUDE_DIR",
             "SDKROOT", "CXXSTDLIB", "LD_LIBRARY_PATH", "LD_PRELOAD", "PKG_CONFIG_LIBDIR", "PKG_CONFIG_SYSROOT_DIR")
# not inputs: the registry location (Cargo.lock pins the sources) and terminal output. CARGO_BUILD_JOBS is
# scheduling only. Measured (docs/ORACLE-SAIL.md "Split build"): the SAIL_SPLIT=1 driver is bit-identical across job counts
# (-j8 and -j24, sha256 d894a505...), so the split binary does not depend on it; it stays KEYED anyway (the SAIL_SPLIT=0
# single-unit driver has no such measurement, and a key that is too fine only costs a rebuild).
ENV_SKIP = ("CARGO_HOME", "CARGO_TERM_COLOR", "CARGO_TERM_PROGRESS_WHEN", "CARGO_TERM_PROGRESS_WIDTH", "CARGO_TERM_VERBOSE", "CARGO_LOG")


def sha(b):
    return hashlib.sha256(b).hexdigest()


def sha_file(p):
    h = hashlib.sha256()
    with open(p, "rb") as f:
        for c in iter(lambda: f.read(1 << 20), b""):
            h.update(c)
    return h.hexdigest()


def run(*cmd):
    try:
        r = subprocess.run(cmd, capture_output=True, text=True, timeout=60)
        return (r.stdout + r.stderr).strip()
    except Exception as ex:
        return "unavailable: %s" % type(ex).__name__


def exe_sha(name):
    """The SHA-256 of the executable `name` resolves to on PATH (a swapped compiler with an unchanged
    --version string is another key), or 'missing'."""
    import shutil
    p = shutil.which(name)
    if not p:
        return "missing"
    try:
        return sha_file(os.path.realpath(p))
    except OSError:
        return "unreadable"


def libgmp():
    out = run("ldconfig", "-p")
    for line in out.splitlines():
        if line.strip().startswith("libgmp.so") and "=>" in line:
            p = os.path.realpath(line.split("=>")[1].strip())
            try:
                return {"path": os.path.basename(p), "sha256": sha_file(p)}
            except OSError:
                pass
    return {"missing": True}


def inputs(root, pins, model_file):
    here = os.path.join(root, "oracle-sail")
    out = {"scheme": SCHEME, "pins": pins, "machine": platform.machine()}
    if model_file:
        out["model.cpp"] = sha_file(model_file)
    out["instrument_model.py"] = sha_file(os.path.join(here, "instrument_model.py"))
    # the parallel model build (SAIL_SPLIT=1): the splitter, the crate-copy maker and the build.rs patch decide what is compiled
    for rel in ("split_model.py", "split_crate.py", "build.rs.patch", "dir_digest.py"):
        out[rel] = sha_file(os.path.join(here, rel))
    srcs = {}
    for rel in ("Cargo.toml", "Cargo.lock", "build.rs", "rust-toolchain", "rust-toolchain.toml",
                ".cargo/config", ".cargo/config.toml"):
        p = os.path.join(here, rel)
        if os.path.isfile(p):
            srcs[rel] = sha_file(p)
    for d, dirs, files in os.walk(os.path.join(here, "src")):
        dirs.sort()
        for f in sorted(files):
            p = os.path.join(d, f)
            srcs[os.path.relpath(p, here)] = sha_file(p)
    for p in (os.path.join(os.environ.get("CARGO_HOME") or os.path.expanduser("~/.cargo"), "config.toml"),
              os.path.join(os.environ.get("CARGO_HOME") or os.path.expanduser("~/.cargo"), "config")):
        if os.path.isfile(p):
            srcs["~/.cargo/" + os.path.basename(p)] = sha_file(p)
    out["sources"] = srcs
    out["rustc"] = run("rustc", "-vV")
    out["cargo"] = run("cargo", "-V")
    cxx = os.environ.get("CXX") or "c++"
    out["cxx"] = run(cxx, "--version")
    # binaries by content, not only by their --version text: rustc and cargo (rustup's proxies resolve to the
    # toolchain through `rustc -vV` above), the C++ compiler, and the `cc` rustc links with
    out["bin"] = {"rustc": exe_sha("rustc"), "cargo": exe_sha("cargo"), "cxx": exe_sha(cxx), "cc": exe_sha(os.environ.get("CC") or "cc"),
                  "ld": exe_sha("ld")}
    out["libgmp"] = libgmp()
    # .cargo/config files in every parent directory of the crate are read by cargo too
    parents = {}
    d = os.path.dirname(os.path.abspath(here))
    while True:
        for rel in (".cargo/config", ".cargo/config.toml"):
            q = os.path.join(d, rel)
            if os.path.isfile(q):
                parents[q] = sha_file(q)
        nd = os.path.dirname(d)
        if nd == d:
            break
        d = nd
    out["parent-cargo-config"] = parents
    out["env"] = {k: v for k, v in sorted(os.environ.items())
                  if (k in ENV_NAMES or k.startswith(ENV_PREFIXES)) and k not in ENV_SKIP}
    return out


def main(argv):
    if not argv:
        sys.exit(__doc__)
    root, pins, model_file, show = argv[0], {}, None, False
    i = 1
    while i < len(argv):
        a = argv[i]
        if a == "--pins":
            i += 1
            while i < len(argv) and "=" in argv[i] and not argv[i].startswith("--"):
                k, v = argv[i].split("=", 1)
                pins[k] = v
                i += 1
            continue
        if a == "--model-file":
            model_file = argv[i + 1]
            i += 2
            continue
        if a == "--show":
            show = True
        i += 1
    obj = inputs(root, pins, model_file)
    if show:
        print(json.dumps(obj, sort_keys=True, indent=1))
    else:
        print(sha(json.dumps(obj, sort_keys=True, separators=(",", ":")).encode())[:40])


if __name__ == "__main__":
    main(sys.argv[1:])
