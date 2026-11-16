#!/usr/bin/env bash
SP=$SP; E=$SP/pairings-stmt
cd $SP/wt-stmt-pairings; export PATH=$HOME/.elan/bin:$PATH; LP=$SP/dl-oleans-2
for d in .lake/packages/*/.lake/build/lib/lean; do LP="$LP:$d"; done
: > $E/seal/summary.txt
for f in $E/seal/probes/*.lean; do LEAN_PATH=$LP lean -DmaxErrors=0 $f > $f.log 2>&1; rc=$?; echo "$(basename $f) rc=$rc errors=$(grep -c "error:" $f.log) unknown=$(grep -c "Unknown constant" $f.log)" >> $E/seal/summary.txt; done
LEAN_PATH=$LP lean $E/probe/AxiomProbe.lean > $E/logs/axioms.txt 2>&1; echo "axiom probe rc=$?" >> $E/seal/summary.txt
