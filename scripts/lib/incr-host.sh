#!/usr/bin/env bash
# incr-host.sh: the digest of everything a lane runs that is NOT in the tree, the Lean toolchain or the keyed environment: the host
# compilers, linkers, assemblers, interpreters and loaders (by the SHA-256 of the resolved binaries), what the compilers read (crt files, libgcc, libc
# scripts, /usr/include, package versions), the environment that steers them (CPATH, CFLAGS, PYTHONPATH, ... by value AND by the content they name),
# the Go toolchain (go, its tool directory, a manifest of GOROOT), and the dependency trees of the ISA-model lanes (manifests).
# Sourced by scripts/lib/incr.sh; the result is one line, `tools=<sha256>[ extra]`, used as lane argument `hosttools:`. Any doubt is a MISS:
# an unreadable name, a cap exceeded, a malformed digest or an unstable (changed while computing) input keys a fresh random value.
# docs/TESTING.md "Keyed and unkeyed inputs" has the argument. Cost: about 2 s uncached, once per gate run through the cache.

_ih_rand() { echo "miss-$RANDOM$RANDOM$RANDOM$RANDOM"; }
_ih_h() { # FILE: sha256 of the file with symlinks resolved, or "absent"
  local r; r="$(readlink -f -- "$1" 2>/dev/null)" || { echo absent; return; }
  if [ -f "$r" ]; then sha256sum -- "$r" 2>/dev/null | cut -c1-64; else echo absent; fi
}
# _ih_tree PATH...: digest of the files of each path (a file; a directory: every regular file below it, symlinks to files AND directories followed,
# names, sizes and SHA-256). At most IH_MAX_FILES files / IH_MAX_BYTES bytes in total: above that a random value (a forced miss).
_ih_tree() {
  local p n=0 b=0 out
  out="$(
    for p in "$@"; do
      if [ -d "$p" ]; then find -L "$p" -type f -printf '%p\t%s\n' 2>/dev/null | LC_ALL=C sort
      elif [ -f "$p" ]; then printf '%s\t%s\n' "$p" "$(stat -L -c %s -- "$p" 2>/dev/null)"
      else printf '%s\tabsent\n' "$p"; fi
    done)"
  [ -n "$out" ] || { echo none; return; }
  n="$(wc -l <<<"$out")"; b="$(awk -F'\t' '{ s += $2 } END { printf "%d", s }' <<<"$out")"
  if [ "$n" -gt "${IH_MAX_FILES:-60000}" ] || [ "$b" -gt "${IH_MAX_BYTES:-3000000000}" ]; then _ih_rand; return; fi
  { printf '%s\n' "$out"; cut -f1 <<<"$out" | grep -v '^$' | tr '\n' '\0' | xargs -0 -r -P 4 -n 200 sha256sum -- 2>/dev/null | LC_ALL=C sort -k2; } | sha256sum | cut -c1-64
}
_ih_gccs() { local n; for n in gcc g++ clang aarch64-linux-gnu-gcc x86_64-linux-gnu-gcc; do type -P -- "$n" 2>/dev/null; done | sort -u; }
_ih_tools() { # every tool whose resolved bytes are keyed
  local n IH_CC0="${CC-}" IH_CXX0="${CXX-}" IH_GOCC IH_GOCXX; IH_GOCC="$(go env CC 2>/dev/null)"; IH_GOCXX="$(go env CXX 2>/dev/null)"; local -a ns=(cc gcc g++ c++ cpp clang clang++ ld ld.bfd ld.gold ld.lld as ar nm objcopy objdump strip ranlib readelf
    aarch64-linux-gnu-gcc aarch64-linux-gnu-g++ aarch64-linux-gnu-as aarch64-linux-gnu-ld aarch64-linux-gnu-objdump aarch64-linux-gnu-objcopy aarch64-linux-gnu-ar aarch64-linux-gnu-nm
    x86_64-linux-gnu-gcc x86_64-linux-gnu-g++ x86_64-linux-gnu-as x86_64-linux-gnu-ld x86_64-linux-gnu-objdump
    python3 python bwrap git make pkg-config ccache distcc go gofmt opam ocaml ocamlfind dune sail z3 rsync flock
    "${IH_CC0%% *}" "${IH_CXX0%% *}" "${IH_GOCC%% *}" "${IH_GOCXX%% *}")
  for n in "${ns[@]}"; do [ -z "$n" ] || echo "$n"; done
  compgen -c qemu- 2>/dev/null | sort -u
}
_ih_bins() { # one "label ... digest" line per input; unsorted
  local n p q g d out dir r
  local IH_CC0="${CC-}" IH_CXX0="${CXX-}" IH_GOCC IH_GOCXX; IH_GOCC="$(go env CC 2>/dev/null)"; IH_GOCXX="$(go env CXX 2>/dev/null)"
  while read -r n; do
    p="$(type -P -- "$n" 2>/dev/null)" || p=""
    if [ -n "$p" ]; then r="$(readlink -f -- "$p")"; echo "tool $n $r $(_ih_h "$p")"; else echo "tool $n absent"; fi
  done < <(_ih_tools)
  # a compiler launcher in front of the build is refused (ccache/distcc hide which compiler ran): a forced miss
  case "${IH_CC0%% *} ${IH_CXX0%% *} ${IH_GOCC%% *} ${IH_GOCXX%% *}" in *ccache*|*distcc*|*icecc*|*sccache*) _ih_rand | sed 's/^/launcher /' ;; esac
  # what each compiler driver reads and runs
  local gd; gd="$(mktemp -d)" || return 1
  while read -r g; do ( _ih_gcc_inputs "$g" > "$gd/$(echo "$g" | tr / _)" ) & done < <(_ih_gccs)
  wait; cat "$gd"/* 2>/dev/null; rm -rf "$gd"
  _ih_bins2
}
_ih_gcc_inputs() { # one compiler driver
  local g=$1 q out
  {
    for q in cc1 cc1plus as ld collect2 lto-wrapper; do
      out="$("$g" -print-prog-name=$q 2>/dev/null)"; [ -n "$out" ] || continue
      [ "${out#/}" != "$out" ] || out="$(type -P -- "$out" 2>/dev/null)"
      echo "prog $g $q $(readlink -f -- "${out:-/nonexistent}" 2>/dev/null) $(_ih_h "${out:-/nonexistent}")"
    done
    for q in crt1.o crti.o crtn.o Scrt1.o crtbegin.o crtend.o crtbeginS.o crtendS.o libgcc.a libgcc_eh.a libgcc_s.so libgcc_s.so.1 liblto_plugin.so libc.so libc.a libm.so libm.a libpthread.a libdl.a libstdc++.so libstdc++.a libc_nonshared.a; do
      out="$("$g" -print-file-name=$q 2>/dev/null)"
      case "$out" in /*) echo "file $g $q $(readlink -f -- "$out" 2>/dev/null) $(_ih_h "$out")" ;; *) echo "file $g $q none" ;; esac
    done
    echo "ver $g $("$g" --version 2>&1 | tr '\n' ' ')"
    echo "dirs $g $("$g" -print-search-dirs 2>&1 | tr '\n' ' ') $("$g" -dumpmachine 2>&1)"
  }
}
_ih_bins2() {
  local n p q d
  for n in ld as ar objdump aarch64-linux-gnu-objdump python3 git make; do p="$(type -P -- "$n" 2>/dev/null)" && echo "ver $n $("$p" --version 2>&1 | head -n 1)"; done
  # the Go toolchain: go (above), the tool directory (compile link asm cgo vet ...), GOROOT's version and sources
  echo "gover $(go version 2>&1)"
  d="$(go env GOTOOLDIR 2>/dev/null)"; [ -n "$d" ] && echo "gotool $(_ih_tree "$d")"
  d="$(go env GOROOT 2>/dev/null)"
  if [ -n "$d" ]; then echo "goroot $(_ih_tree "$d/VERSION" "$d/src" "$d/pkg/include" "$d/bin" "$d/go.env" "$d/lib")"; fi
  # the loader, libc and the system's include files / link-time package versions
  for p in /lib64/ld-linux-*.so.* /lib/ld-linux-*.so.* /lib/*-linux-gnu/ld-linux-*.so.* /lib/*-linux-gnu/libc.so.6 /lib64/libc.so.6 /usr/lib/*-linux-gnu/libc.so.6; do
    [ -e "$p" ] && echo "ldso $(readlink -f -- "$p") $(_ih_h "$p")"
  done
  p="$(type -P -- janus 2>/dev/null || echo bin/janus)"
  ldd "$p" 2>/dev/null | awk '$1 ~ /libc\.so|ld-linux/ { print $(NF-1) }' | while read -r q; do [ -e "$q" ] && echo "ldd $(readlink -f -- "$q") $(_ih_h "$q")"; done
  echo "ldconf $(_ih_tree /etc/ld.so.preload /etc/ld.so.conf /etc/ld.so.conf.d /etc/ld.so.cache)"
  echo "include $(_ih_tree /usr/include)"
  echo "dpkg $(dpkg-query -W -f '${Package} ${Version}\n' 'libc6*' 'libgcc-*' 'libstdc++-*' 'linux-libc-dev*' 'gcc-*' 'g++-*' 'binutils*' 'libc-dev*' 2>/dev/null | LC_ALL=C sort | tr '\n' ';')"
}
# the compiler/interpreter-steering environment, by value and by the content it names
_ih_env() {
  local v n val q
  for v in CPATH C_INCLUDE_PATH CPLUS_INCLUDE_PATH OBJC_INCLUDE_PATH LIBRARY_PATH COMPILER_PATH GCC_EXEC_PREFIX CFLAGS CXXFLAGS CPPFLAGS LDFLAGS \
           BASH_ENV ENV PYTHONPATH PYTHONSTARTUP PYTHONHOME DEPS X86DEPS OPAMROOT ASL_CACHE MAKEFLAGS MAKEFILES SOURCE_DATE_EPOCH CC CXX AS LD AR \
           GIT_CONFIG GIT_CONFIG_GLOBAL GIT_EXEC_PATH PKG_CONFIG_PATH PKG_CONFIG_LIBDIR; do
    if [ -n "${!v+x}" ]; then
      val="${!v}"; echo "env $v=$val"
      case "$v" in
        CPATH|C_INCLUDE_PATH|CPLUS_INCLUDE_PATH|OBJC_INCLUDE_PATH|LIBRARY_PATH|COMPILER_PATH|PYTHONPATH|PKG_CONFIG_PATH|PKG_CONFIG_LIBDIR)
          for q in ${val//:/ }; do [ -z "$q" ] || echo "envnames $v $q $(_ih_tree "$q")"; done ;;
        BASH_ENV|ENV|PYTHONSTARTUP|GIT_CONFIG|GIT_CONFIG_GLOBAL|GCC_EXEC_PREFIX|PYTHONHOME|GIT_EXEC_PATH|ASL_CACHE) [ -z "$val" ] || echo "envnames $v $(_ih_tree "$val")" ;;
      esac
    fi
  done
  # every other PYTHON*, CCACHE_*, DISTCC_*, OPAM* , GCC_* , COMPILER_*  variable by value
  while IFS= read -r n; do
    case "$n" in CCACHE_*|DISTCC_*|PYTHON*|OPAM*|GCC_*|ICECC*) echo "env $n=${!n}" ;; esac
  done < <(compgen -e | LC_ALL=C sort)
}
# the dependency trees the model lanes read (manifests: file list + sizes + SHA-256), and the prebuilt artifacts
_ih_deps() {
  local deps="${DEPS:-/srv/janus-asl-deps}" x86="${X86DEPS:-/srv/janus-x86-deps}" root="${IH_ROOT:-.}" d s
  echo "x86deps $(_ih_tree "$x86")"
  echo "modelpin $(_ih_tree /srv/janus-model-pin)"
  # the ARM Sail sources and the opam switches' executables (the Sail binary and the OCaml compiler it runs with)
  s=(); for d in "$deps"/sail-arm-*/arm-v9.4-a/src; do [ ! -d "$d" ] || s+=("$d"); done
  echo "sailarm $(_ih_tree ${s[@]+"${s[@]}"})"
  s=(); for d in "$deps"/opam/*/bin "$deps"/opam/*/.opam-switch/switch-state "$deps"/opam/config; do [ ! -e "$d" ] || s+=("$d"); done
  echo "opam $(_ih_tree ${s[@]+"${s[@]}"})"
  # artifacts/<Name> (the extracted example binaries the rounds scripts read): everything but the gate's private trees and temporary directories
  echo "artifacts $( { [ -d "$root/artifacts" ] && find -L "$root/artifacts" -type f -not -path "$root/artifacts/gate/*" -not -name 'incr-hosttools.*' -not -path '*/test-incr-*' -not -path '*/incr-liveness.*' -printf '%P\t%s\n' 2>/dev/null | LC_ALL=C sort | while IFS=$'\t' read -r f z; do printf '%s\t%s\t%s\n' "$f" "$z" "$(_ih_h "$root/artifacts/$f")"; done; } | sha256sum | cut -c1-64)"
}
# the stamp of the inputs of the cached digest: the path, inode, size and mtime/ctime of every hashed regular file (the tools and files), plus the environment strings
_ih_stamp() {
  { printf '%s\0' "$PATH" "${CC-}" "${CXX-}" "${DEPS-}" "${X86DEPS-}" "$(pwd)"; _ih_tools | while read -r n; do type -P -- "$n" 2>/dev/null; done | sort -u | while read -r p; do stat -L -c '%n %i %s %.9Y %.9Z' -- "$p" 2>/dev/null; done; _ih_env | sha256sum; } | sha256sum | cut -c1-64
}
# incr_hosttools [--nocache]: one line. The expensive part is cached for the whole gate run in INCR_HOSTTOOLS_CACHE (a private file made by scripts/gate.sh)
# only when its stamp still matches; --nocache recomputes everything (incr_end compares it with the digest the lane started with).
incr_hosttools() {
  local c="${INCR_HOSTTOOLS_CACHE:-}" stamp line="" w q n
  if [ "${1:-}" != --nocache ] && [ -n "$c" ] && [ -s "$c" ]; then
    stamp="$(_ih_stamp)"
    [ "$(sed -n 1p "$c")" != "$stamp" ] || line="$(sed -n 2p "$c")"
    [[ "$line" =~ ^[0-9a-f]{64}$ ]] || line=""
  fi
  if [ -z "$line" ]; then
    line="$( { _ih_bins 2>/dev/null; _ih_env 2>/dev/null; _ih_deps 2>/dev/null; } | LC_ALL=C sort | sha256sum | cut -c1-64)"
    [[ "$line" =~ ^[0-9a-f]{64}$ ]] || line="$(_ih_rand)"
    if [ "${1:-}" != --nocache ] && [ -n "$c" ] && [ -w "$c" ] && [[ "$line" =~ ^[0-9a-f]{64}$ ]]; then printf '%s\n%s\n' "$(_ih_stamp)" "$line" > "$c"; fi
  fi
  w=""
  if [ -n "${LD_PRELOAD:-}" ]; then
    w+="preload=${LD_PRELOAD}"
    for q in ${LD_PRELOAD//:/ }; do
      if [ -f "$q" ] && [ -r "$q" ]; then w+=" $(_ih_h "$q")"; else w+=" unresolved-$(_ih_rand)"; fi
    done
  fi
  if [ -n "${LD_LIBRARY_PATH:-}" ]; then
    w+=" libpath=${LD_LIBRARY_PATH}"
    for q in ${LD_LIBRARY_PATH//:/ }; do
      if [ -e "$q" ]; then w+=" $(_ih_tree "$q")"; else w+=" nodir"; fi
    done
  fi
  printf 'tools=%s%s\n' "$line" "$w"
}
