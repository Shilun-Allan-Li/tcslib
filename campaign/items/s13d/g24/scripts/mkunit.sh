#!/usr/bin/env bash
# Assemble the unit from its header and part files (read-only on everything else).
G="$1"
cd "$G" && cat parts/unit.head parts/Z.head parts/Z.body parts/M1.head parts/M1.body \
  parts/M2.head parts/M2.body parts/C1.head parts/C1.body parts/C2.head parts/C2.body \
  parts/T.head parts/T.body parts/R.head parts/R.body > G24Statements.lean
