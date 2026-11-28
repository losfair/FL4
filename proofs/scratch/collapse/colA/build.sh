#!/bin/bash
# collapse A / B3 (afkprover): x86 root build (+ per-module RSS, + axint27b3.lean), MODE=a64, then the whole-environment
# sweeps collapse/axall.lean / axallA64.lean. Run from the mirror's repo root. SEED: absolute path of a built .lake.
mkdir -p afklogs colAback; S=${SEED:-/data/fl4/lake/FL4-int27}
free -g | head -2
MODE=build NAX=100000 AX=${AXF:-proofs/scratch/collapse/colA/axint27b3.lean} SEED=$S bash proofs/scratch/int27/rssrun.sh > afklogs/colA-build.out 2>&1; echo BUILD_EXIT $?
grep -E '^(SEEDED|SEEDFAIL|BUILD|ERRORS|SORRY|JOBS|OLEANS|AX|RSS_OVER)' afklogs/colA-build.out
grep -E 'Build completed|error: build failed' afklogs/b-build.log | tail -2
grep -E '^error' afklogs/b-build.log | head -40
if [ "${SKIPA64:-0}" != 1 ]; then
MODE=a64 SEED=$S bash /data/fl4/afk-build.sh > afklogs/colA-a64.out 2>&1; echo A64_EXIT $?
grep -E '^(BUILD|ERRORS|SORRY|JOBS)' afklogs/colA-a64.out
grep -E 'Build completed|error: build failed' afklogs/b-a64.log | tail -2
for f in collapse/axall collapse/axallA64; do b=$(basename $f); bash proofs/scratch/int27/axrun.sh scratch/$f.lean afklogs/colA-$b.out; grep -E 'AXALL|error' afklogs/colA-$b.out | cut -c1-400 | head -4; done
fi
free -g | head -2
cp afklogs/colA-*.out afklogs/b-build.log afklogs/b-a64.log afklogs/rss-build.txt colAback/ 2>/dev/null
