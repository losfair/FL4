# Regenerate Fl4Proofs/P3/SpecInvValidMachineTimeGen.lean: the spec's call graph (cg.py -> cg.json),
# the bottom-up order (topo.py's output, setFlags moved before invokeFl4Tcb by hand: order.txt),
# the lemmas (gen2.py: generated statements + hand-written man/*.lean).
cd $(dirname $0); python3 cg.py > /dev/null && python3 gen2.py
