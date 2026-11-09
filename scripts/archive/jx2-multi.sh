#!/usr/bin/env bash
# jx2-multi.sh ISA Name... : verify sequentially, one line each
isa=$1; shift
for n in "$@"; do /srv/janus-jx2/scripts/jx2-verify.sh $isa $n 2>&1 | cut -c1-300; done
