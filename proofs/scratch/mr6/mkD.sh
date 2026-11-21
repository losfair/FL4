cd $(dirname $0)/../..; { cat scratch/mr6/headD.lean; python3 scratch/mr6/mkdgen.py scratch/mr6/fin_order.txt; printf 'end\n\nend Fl4Proofs.P3\n'; } > Fl4Proofs/P3/MachKeepD.lean
