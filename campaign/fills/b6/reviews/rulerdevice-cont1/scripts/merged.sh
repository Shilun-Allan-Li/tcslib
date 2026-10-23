#!/usr/bin/env bash
# The campaign's merged-tree replay list: the downstream closure, over the tip's import graph, of
# every TCSlib .lean file changed from e9e97970 (oleans-l132b's tree) to the tip, plus this landing.
S=$S
R=$S/review/f5-cont1-fill; M=<repo>; T=${1:-b74474925765a06447c8358cb630557598dad16d}
G=${2:-$R/out/graph-tip.json}; OUT=${3:-$R/out/43-merged-replay-from-l132b.txt}
CH=$(git -C $M diff --name-only e9e97970 $T -- 'TCSlib/*.lean' 'TCSlib.lean' | sed 's/\.lean$//')
echo "TCSlib Lean files changed from e9e97970 (oleans-l132b's tree, $(git -C $M rev-parse e9e97970:TCSlib | cut -c1-8)) to $T: $(echo $CH | wc -w)"
echo "$CH" | sed 's/^/  /'
python3 -I $S/g5x-closure.py $G $OUT $CH TCSlib/Complexity/TuringMachine/Build/InputDevice
echo "merged-tree replay list from oleans-l132b (these changes and this landing): $(wc -l < $OUT | tr -d ' ') modules; root TCSlib listed: $(grep -cx TCSlib $OUT)"
sed 's/^/  /' $OUT
python3 -I $S/g5x-closure.py $G $OUT.without $CH > /dev/null
echo "without this landing: $(wc -l < $OUT.without | tr -d ' ') modules; this landing adds: $(comm -13 <(sort $OUT.without) <(sort $OUT) | paste -sd' ' -)"
