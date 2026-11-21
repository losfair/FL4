#!/bin/sh
# usage (mirror root): [SEED=1] [AX=file.lean] sh proofs/scratch/mr4build.sh Mod1 Mod2 ...
export PATH=$HOME/.elan/bin:$PATH
if [ -n "$SEED" ] || [ ! -d proofs/.lake/build ]; then
  mkdir -p proofs/.lake && rm -rf proofs/.lake/build && cp -cR ../${SRC:-FL4-audit}/proofs/.lake/build proofs/.lake/build && { [ -d proofs/.lake/packages ] || cp -cR ../${SRC:-FL4-audit}/proofs/.lake/packages proofs/.lake/packages; }
  echo seeded
fi
mkdir -p proofs/.deps; [ -e proofs/.deps/aeneas ] || ln -s $(cd ..; pwd)/fl4-aeneas/backends/lean proofs/.deps/aeneas
cd proofs
for m in "$@"; do
  echo "== $m"; date
  nice -n 5 lake build Fl4Proofs.P3.$m > ../mr4-build.log 2>&1 || { grep -n -A20 '^error' ../mr4-build.log | cut -c1-240 | head -260; echo ====; grep '^error' ../mr4-build.log | cut -c1-200; exit 1; }
  tail -2 ../mr4-build.log
done
if [ -n "$AX" ]; then nice -n 5 lake env lean "$AX" 2>&1 | head -80; fi
date
