cd $(dirname $0); python3 mtgen.py . && { cat head.lean; cat body.lean; cat tail.lean; printf '\nend\n\nend Fl4Proofs.P3.MachT\n'; } > ../../Fl4Proofs/P3/MachFieldFamT.lean
