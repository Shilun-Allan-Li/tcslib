#!/usr/bin/env bash
S=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad
R=$S/review/c1-core-cont2; cd $R/out || exit 1
mk() { out=$1; shift; python3 -I -B $S/wt-hk/devtools/seyoon/mkdownmulti.py $R/wt-tip $S/wt-hk/devtools/seyoon $out "$@" > /dev/null; }
mk 38-replay-from-lu2sc1.txt TCSlib.Complexity.TuringMachine.NDCodeSimulator TCSlib.Complexity.TuringMachine.UniversalK TCSlib.Complexity.TuringMachine
mk 38-down-pr149.txt TCSlib.Complexity.TuringMachine.Deterministic TCSlib.Complexity.TuringMachine.Finite
mk 38-down-pr147.txt TCSlib.Complexity.TuringMachine.UniversalK
mk 38-down-item2.txt TCSlib.Complexity.Diagonalization.NTimeHierarchy
mk 38-down-item3.txt TCSlib.Complexity.TuringMachine.CodeSimulator
{ echo "# downstream closures in the landing tree (tip 97299639 + the delivered NDCodeSimulator), root TCSlib excluded"
  for f in 38-down-tip 38-replay-from-lu2sc1 38-down-pr149 38-down-pr147 38-down-item2 38-down-item3; do
    echo "$f: $(wc -l < $f.txt | tr -d ' ') modules; in common with R's closure: $(comm -12 <(sort $f.txt) <(sort 38-down-tip.txt) | tr '\n' ' ')"; done
  echo; echo "replay list from a copy of oleans-lu2sc1 (closure of NDCodeSimulator, UniversalK and the facade, the files differing from lu2sc1's tree 28150fc1):"; cat 38-replay-from-lu2sc1.txt; } > 38-merged-replay.txt
