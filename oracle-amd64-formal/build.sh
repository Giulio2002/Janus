#!/usr/bin/env bash
# Build the Sail x86 single-step emulator used by compare.py, entirely in user space.
# Usage: oracle-amd64-formal/build.sh WORKDIR     (WORKDIR gets gmp, m4, an opam root, the model)
set -euo pipefail
W="$(realpath -m "${1:?usage: build.sh WORKDIR}")"; mkdir -p "$W"; cd "$W"
L="$W/local"; export PATH="$L/bin:$PATH"
# 1. m4 and GMP (the host has neither m4 nor GMP headers; GCC 15 needs -std=gnu17 for GMP 6.3)
[ -x "$L/bin/m4" ] || { curl -sLO https://ftp.gnu.org/gnu/m4/m4-1.4.19.tar.xz; tar xf m4-1.4.19.tar.xz
  (cd m4-1.4.19 && CC="gcc -std=gnu17" ./configure --prefix="$L" >/dev/null && make -j16 >/dev/null && make install >/dev/null); }
[ -f "$L/include/gmp.h" ] || { curl -sLO https://ftp.gnu.org/gnu/gmp/gmp-6.3.0.tar.xz; tar xf gmp-6.3.0.tar.xz
  (cd gmp-6.3.0 && CC="gcc -std=gnu17" ./configure --prefix="$L" >/dev/null && make -j16 >/dev/null && make install >/dev/null); }
export C_INCLUDE_PATH="$L/include" LIBRARY_PATH="$L/lib" LD_LIBRARY_PATH="$L/lib" PKG_CONFIG_PATH="$L/lib/pkgconfig"
# 2. Sail 0.20.3 from opam, in a private opam root, on the system OCaml (5.4.0)
export OPAMROOT="$W/opam" OPAMYES=1
[ -d "$OPAMROOT" ] || opam init --bare -n --disable-sandboxing >/dev/null
opam switch list 2>/dev/null | grep -q '^. *sail ' || opam switch create sail ocaml-system >/dev/null
eval "$(opam env --switch=sail)"
command -v sail >/dev/null || opam install sail -j 24 >/dev/null
# 3. The model snapshot (rems-project/sail-x86-from-acl2 @ 0c6c023, Nov 2024)
[ -d sail-x86-from-acl2 ] || git clone -q https://github.com/rems-project/sail-x86-from-acl2
git -C sail-x86-from-acl2 checkout -q 0c6c023dccc7c20d8d9dbfc481f01d9bb49d62bf
rm -rf model-janus; cp -r sail-x86-from-acl2/model model-janus; cd model-janus
# 4. Patches: undefined values come from a config register (0 or 1); main executes one step.
python3 - <<'PY'
s = open('prelude.sail').read()
s = s.replace("val undef_read_logic : unit -> nat\nfunction undef_read_logic () = undefined",
              "register undef_val : nat\nval undef_read_logic : unit -> nat\nfunction undef_read_logic () = undef_val")
open('prelude.sail', 'w').write(s)
s = open('config.sail').read()
s = s.replace('function clause __SetConfig("cr4"',
  'function clause __SetConfig("undef", value) = { undef_val = if value >= 0 then value else 0 }\nfunction clause __SetConfig("cr4"')
open('config.sail', 'w').write(s)
# FS base: 64-bit-mode FS-relative addressing (segment_base_and_bounds, ea_to_la) reads
# msrs[1] (IA32_FS_BASE); seg_hidden_bases[4] (FS) is set too for completeness.
# ymm{i}q{j}: quadword j (bits 64j+63..64j) of zmm{i}, i < 16, j < 4.
cl = ['function clause __SetConfig("fsbase", value) = { let v = get_slice_int(64, value, 0); msrs[1] = v; seg_hidden_bases[4] = v }']
for i in range(16):
    for j in range(4):
        cl.append(f'function clause __SetConfig("ymm{i}q{j}", value) = {{ zmms[{i}] = [zmms[{i}] with {64*j+63} .. {64*j} = get_slice_int(64, value, 0)] }}')
s = s.replace('function clause __SetConfig("cr4"', '\n'.join(cl) + '\nfunction clause __SetConfig("cr4"')
open('config.sail', 'w').write(s)
# printState also prints bits 255:0 of zmm0..zmm15 as "ymmI = 0x<64 hex digits>".
s = open('logging.sail').read()
s = s.replace('\tprint_bits("rip = ", read_rip());\n}',
  '\tprint_bits("rip = ", read_rip());\n' +
  ''.join(f'\tprint_bits("ymm{i} = ", zmms[{i}][255 .. 0]);\n' for i in range(16)) + '}', 1)
open('logging.sail', 'w').write(s)
s = open('main.sail').read()
s = s[:s.index("// A main function for C compilation")] + '''// Janus oracle: execute exactly one instruction and print the state.
val main : unit -> unit
function main () = {
	initialize_model();
	try {
		x86_fetch_decode_execute();
		print_endline("STATUS ok");
	} catch {
		Emsg(msg) => { print_endline("STATUS error " + msg) }
	};
	printState();
}
'''
open('main.sail', 'w').write(s)
PY
S="prelude.sail register_types.sail registers.sail register_accessors.sail opcode_ext.sail memory_accessors.sail init.sail config.sail logging.sail step.sail main.sail"
sail -c -o x86_emulator $S 2>/dev/null
SD="$(opam var sail:share)"
gcc -O2 -DHAVE_SETCONFIG x86_emulator.c "$SD"/lib/*.c -lgmp -lz -I "$SD/lib" -o x86_emulator 2>/dev/null
echo "built $W/model-janus/x86_emulator"
