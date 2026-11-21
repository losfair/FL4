#!/bin/bash
# g2i build: module build of the given P3 modules (seeds the mirror if cold); greps sorry over the changed files; optional axioms file $AX
set -o pipefail
export PATH=$HOME/.elan/bin:$PATH
if [ ! -d proofs/.lake/build/lib ]; then mkdir -p proofs/.lake && rm -rf proofs/.lake/build && cp -cR ../FL4-audit/proofs/.lake/build proofs/.lake/build && { [ -d proofs/.lake/packages ] || cp -cR ../FL4-audit/proofs/.lake/packages proofs/.lake/packages; }; fi
mkdir -p proofs/.deps; [ -e proofs/.deps/aeneas ] || ln -s $(cd ..; pwd)/fl4-aeneas/backends/lean proofs/.deps/aeneas
grep -n "sorry\|admit\|native_decide\|bv_decide" $(cat g2i.files 2>/dev/null) /dev/null | grep -v "^.*:.*--"
cd proofs
args=""; for m in "$@"; do args="$args Fl4Proofs.P3.$m"; done
timeout ${TMO:-3000} nice -n 5 lake build $args 2>&1 | tee ../build.log | grep --line-buffered -a "^error" | awk "{print substr(\$0,1,200); fflush()}"
rc=${PIPESTATUS[0]}
if [ $rc -ne 0 ] || grep -q "^error" ../build.log; then echo ====; awk -v C=${ECTX:-4} '/^error/{print; n=C; g=40; next} /^(warning|info)/{n=0; g=0; next} n>0{print; n--; next} g>0 && /⊢/{print; g=0; next} g>0{g--}' ../build.log | grep -v "linter" | cut -c1-200 | head -${ELINES:-400}; grep -c '^error' ../build.log; exit 1; fi
tail -2 ../build.log
if [ -n "$AX" ]; then lake env lean "$AX" 2>&1 | cut -c1-240; fi
