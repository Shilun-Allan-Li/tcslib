#!/usr/bin/env bash
# stage.sh <folder-name> <bundle-name> <lean-rev> <records-rev> <list-file> <readme-intro-file> <findings-name>
set -euo pipefail
S="${TCSLIB_SCRATCH:-$HOME/.tcslib-scratch}"
H=$S/wt-hk; NAME=$1; B=$2; L=$(git -C $H rev-parse $3); O=$(git -C $H rev-parse $4); LIST=$5; INTRO=$6; FIND=$7
W=$S/stage/$NAME; F=${TCSLIB_REPO:-$HOME/tcslib}/exchange/outbox/gates/$NAME
[ ! -e "$F" ] || { echo "exists: $F" >&2; exit 2; }
mkdir -p $W; cp $LIST $W/BUNDLE-FILES.txt
while read -r p; do r=$O; [ "${p#TCSlib/}" != "$p" ] && r=$L; git -C $H cat-file -e $r:$p 2>/dev/null || { echo "MISSING $p" >&2; exit 2; }; done < $W/BUNDLE-FILES.txt
python3 -I $H/devtools/seyoon/mkbundle-mixed.py $H $L $O $W/$B $W/BUNDLE-FILES.txt
python3 -I $H/devtools/seyoon/mkbundle-mixed.py $H $L $O $W/$B $W/BUNDLE-FILES.txt --verify
rm -rf $W/export; mkdir -p $W/export; git -C $H archive $O | tar -x -C $W/export; git -C $H archive $L TCSlib | tar -x -C $W/export
V=$(python3 -I $H/devtools/seyoon/verifybundle.py $W/export $W/$B $W/BUNDLE-FILES.txt | tail -1); echo "$V"
echo "$V" | grep -q "0 problems"
N=$(wc -l < $W/BUNDLE-FILES.txt | tr -d ' '); SZ=$(wc -c < $W/$B | tr -d ' '); SHA=$(shasum -a 256 $W/$B | cut -d' ' -f1)
mkdir -p $F; cp $W/$B $W/BUNDLE-FILES.txt $F/
{ echo "# $NAME"; echo; cat $INTRO; echo
  echo "| File | What |"; echo "|---|---|"
  echo "| \`$B\` | the bundle to attach: $N sections (one per file, in \`BUNDLE-FILES.txt\` order), $SZ bytes |"
  echo "| \`BUNDLE-FILES.txt\` | the section order |"; echo "| \`SHA256SUMS\` | SHA-256 of the bundle and of this README |"; echo "| \`README.md\` | this file |"; echo
  echo "- **Bundle SHA-256:** \`$SHA\`"
  echo "- **Built by** \`mkbundle-mixed.py\`: the Lean files from \`$L\`, everything else from the"
  echo "  campaign commit \`$O\`."
  echo "- **Checked by** its \`--verify\` rebuild, and by \`verifybundle.py\` against a \`git archive\` export of"
  echo "  the two: \`$N segments, 0 problems\`."
  echo "- **Findings:** the auditor delivers \`$FIND\`; committed as \`campaign/gates/${NAME%-gate}/findings.md\`."
  echo "- **Not yet dispatched.** The prompt to paste is given in chat (no PROMPT.txt)."; } > $F/README.md
( cd $F && shasum -a 256 $B README.md > SHA256SUMS )
echo "STAGED $NAME $SHA $N $SZ"
