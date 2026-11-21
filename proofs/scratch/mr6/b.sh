#!/bin/sh
# usage (mirror root): sh proofs/scratch/mr6/b.sh Mod...   (compact errors)
export PATH=$HOME/.elan/bin:$PATH
mkdir -p proofs/.deps; [ -e proofs/.deps/aeneas ] || ln -s $(cd ..; pwd)/fl4-aeneas/backends/lean proofs/.deps/aeneas
cd proofs
for m in "$@"; do
  echo "== $m"
  nice -n 5 lake build Fl4Proofs.P3.$m > ../mr6-build.log 2>&1 || { grep -n -A14 '^error' ../mr6-build.log | grep -v "deprecated\|Hint" | cut -c1-260 | head -${N:-150}; tail -3 ../mr6-build.log; exit 1; }
  tail -1 ../mr6-build.log
done
if [ -n "$AX" ]; then nice -n 5 lake env lean "$AX" 2>&1 | head -60; fi
