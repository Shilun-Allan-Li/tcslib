set -u
source "$(dirname "$0")/lib.sh"
G=$GATE
d=screen
for side in BASE HEAD; do
  rev=$BASE; pop=$G/POPULATION-BASE.txt
  [ $side = HEAD ] && rev=$HEAD && pop=$G/POPULATION.txt
  out=$G/$d/$side; rm -rf "$out"; mkdir -p $out/export
  git -C $REPO archive $rev scripts/copy-text-screen-v3.py $(cat $pop) | tar -x -C $out/export
  (cd $out/export && python3 -I scripts/copy-text-screen-v3.py . $(cat $pop) > ../screen.txt 2> ../screen.err; echo "$d $side exit $?")
  grep -E "declarations screened|copy pairs|reproduced" $out/screen.txt
done
python3 -I $REPO/devtools/seyoon/pairdiff.py $G/$d/HEAD/screen.txt $G/$d/BASE/screen.txt > $G/$d/pairdiff.txt; echo "$d pairdiff exit $?"; wc -l < $G/$d/pairdiff.txt
