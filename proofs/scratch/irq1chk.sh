#!/bin/sh
# usage (mirror root): sh proofs/scratch/irq1chk.sh File.lean [deps...]  -- build deps, then check one file
export PATH=$HOME/.elan/bin:$PATH
mkdir -p proofs/.deps; [ -e proofs/.deps/aeneas ] || ln -s $(cd ..; pwd)/fl4-aeneas/backends/lean proofs/.deps/aeneas
f=$1; shift
if [ $# -gt 0 ]; then sh proofs/scratch/kp1build.sh "$@" || exit 1; fi
A=12 N=300 sh proofs/scratch/kp17err.sh "$f"
