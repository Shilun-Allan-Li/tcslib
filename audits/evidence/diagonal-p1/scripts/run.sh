#!/usr/bin/env bash
# Diagonal Part 1: rebuild the landing tree and re-run every check, fail-closed.
# Usage: bash run.sh <S> <repo> [<snapshot>]
#   <S>        the scratchpad (holds tools/leanelab.sh, wt-u2 for the Lean packages)
#   <repo>     the tcslib clone, used read-only (git rev-parse, cat-file, ls-tree, hash-object
#              without -w, archive) by the precheck and the name screen only
#   <snapshot> the olean tree (default <S>/oleans-lh1; at landing, the tip's snapshot)
# `lean` only through <S>/tools/leanelab.sh (no -o, no olean written); python3 -I; diff/patch on
# scratch copies; nothing is written outside <S>/diag-p1. Any failed step stops the run.
set -euo pipefail
S="$1"; REPO="$2"; D="$S/diag-p1"; SC="$D/scripts"; W="$D/work"; LG="$D/logs"
BASE_REV=cd450a526e71a5e437ebe84245ea958bf309eda1
BASE_SHA=ab89c9578b230a19c127c9f3508bad453e01c79c9afb3f52e712336c5fb5ef17
REL=TCSlib/Complexity/TimeHierarchy/Diagonal.lean
OL="${3:-$S/oleans-lh1}"; WT="$S/wt-u2"; ELAB="$S/tools/leanelab.sh"
IMPORTERS=(Diagonalization.EXPCOM Diagonalization.NotTimeConstructible SpaceComplexity.Hierarchy
           TimeHierarchy.Separation TimeHierarchy)
san() { sed "s|$D|<D>|g; s|$S|<S>|g"; }
pass=0
ok() { pass=$((pass + 1)); echo "PASS $pass: $1" | tee -a "$LG/summary.log"; }
mkdir -p "$LG" "$W"; : > "$LG/summary.log"

# ---- 0. precheck ------------------------------------------------------------------------------
tip=$(git -C "$REPO" rev-parse origin/complexity/arora-barak-ch3-4)
[ "$(cat "$D/base/HEAD")" = "$BASE_REV" ] || { echo "precheck: base/HEAD is not $BASE_REV"; exit 1; }
[ "$(git -C "$REPO" cat-file -p "$BASE_REV:$REL" | shasum -a 256 | cut -d' ' -f1)" = "$BASE_SHA" ] \
  || { echo "precheck: $REL at $BASE_REV has an unexpected hash"; exit 1; }
[ "$(shasum -a 256 "$D/base/$REL" | cut -d' ' -f1)" = "$BASE_SHA" ] \
  || { echo "precheck: the exported base file differs from the commit"; exit 1; }
# the whole exported tree (TCSlib/, TCSlib.lean) has the commit's blob hashes (hash-object reads,
# never writes: no -w), and so does the exported lint script
(cd "$D/base" && find TCSlib TCSlib.lean -type f | LC_ALL=C sort) > "$W/paths.lst"
sed "s|^|$D/base/|" "$W/paths.lst" | git -C "$REPO" hash-object --no-filters --stdin-paths \
  > "$W/hashes.lst"
paste -d' ' "$W/hashes.lst" "$W/paths.lst" | sort -k2 > "$W/export.idx"
git -C "$REPO" ls-tree -r "$BASE_REV" TCSlib TCSlib.lean | awk '{print $3" "$4}' | sort -k2 \
  > "$W/commit.idx"
cmp -s "$W/export.idx" "$W/commit.idx" || { echo "precheck: exported tree differs"; exit 1; }
[ "$(git -C "$REPO" hash-object --no-filters "$D/base/scripts/style_lint.py")" = \
  "$(git -C "$REPO" rev-parse "$BASE_REV:scripts/style_lint.py")" ] \
  || { echo "precheck: exported style_lint.py differs"; exit 1; }
[ -x "$ELAB" ] || [ -f "$ELAB" ] || { echo "precheck: $ELAB missing"; exit 1; }
[ -f "$OL/TCSlib/Complexity/TimeHierarchy/Diagonal.olean" ] || { echo "precheck: snapshot"; exit 1; }
ls -d "$WT"/.lake/packages/*/.lake/build/lib/lean > /dev/null || { echo "precheck: packages"; exit 1; }
{ echo "base $BASE_REV (exported read-only by git archive into <D>/base)"
  echo "campaign tip now: $tip"
  if [ "$tip" != "$BASE_REV" ]; then
    echo "tip moved; Lean files changed since the base:"
    git -C "$REPO" diff --name-only "$BASE_REV" "$tip" -- '*.lean' | sed 's/^/  /'
  fi
  echo "snapshot: $OL; packages: <S>/wt-u2/.lake/packages" | san; } > "$LG/precheck.log"
if [ "$tip" != "$BASE_REV" ]; then
  # the tip moved: the landing stays valid only if tipcheck.py's conditions (a)-(c) hold
  rm -rf "$W/tip"; mkdir -p "$W/tip"
  git -C "$REPO" diff --name-status "$BASE_REV" "$tip" -- '*.lean' > "$W/tip-name-status.txt"
  while read -r st path; do
    [ "${st:0:1}" = D ] && continue
    mkdir -p "$W/tip/$(dirname "$path")"; git -C "$REPO" cat-file -p "$tip:$path" > "$W/tip/$path"
  done < <(awk '{print $1" "$NF}' "$W/tip-name-status.txt")
  python3 -I "$SC/tipcheck.py" "$D/base" "$W/tip" "$W/tip-name-status.txt" "$D/replay-order.txt" \
    >> "$LG/precheck.log" || { echo "precheck: the tip moved and the landing is not valid there"; exit 1; }
fi
tipnote="the tip is the base"
[ "$tip" != "$BASE_REV" ] && tipnote="the tip moved to ${tip:0:8}; the landing is valid there (tipcheck.py)"
ok "precheck (base commit and file hash; the exported tree's $(wc -l < "$W/commit.idx" | tr -d " ") blobs; snapshot; packages; $tipnote)"

# ---- 1. the landed file, rebuilt and compared -----------------------------------------------
python3 -I "$SC/mklanded.py" "$D/base/$REL" "$W/Diagonal.landed.lean" | san > "$LG/mklanded.log"
cmp "$W/Diagonal.landed.lean" "$D/tree/$REL"
ok "landed file rebuilt by 11 asserted edits, byte-identical to tree/"

# ---- 2. the patch replays ---------------------------------------------------------------------
rm -rf "$W/patchcheck"; mkdir -p "$W/patchcheck/$(dirname "$REL")"
cp "$D/base/$REL" "$W/patchcheck/$REL"
(cd "$W/patchcheck" && patch -p1 -s < "$D/patches/Diagonal.patch")
cmp "$W/patchcheck/$REL" "$D/tree/$REL"
ok "patches/Diagonal.patch replays on the base byte for byte"

# ---- 3. import graph and replay order --------------------------------------------------------
PK=$(ls -d "$WT"/.lake/packages/*/.lake/build/lib/lean | tr '\n' ':')
python3 -I "$SC/graph.py" "$D/base" "$OL" "$PK" "$W/graph" | san > "$LG/graph.log"
cmp "$W/graph/replay-order.txt" "$D/replay-order.txt"
! grep -qx "TCSlib" "$D/replay-order.txt"
ok "replay-order.txt regenerated identically (topological, root excluded, imports covered)"

# ---- 4. freeze, names, widths and hygiene, lint ----------------------------------------------
python3 -I "$SC/freeze.py" "$D/base/$REL" "$D/tree/$REL" > "$LG/freeze.log"
ok "freeze (received heads byte-identical, header identical, no admission)"
# the name screen runs on the base and again on the tip's whole tree (gate m1: unrelated files
# may change between them); the tip's Diagonal.lean must still be the base's
rm -rf "$W/tipexport"; mkdir -p "$W/tipexport"
git -C "$REPO" archive "$tip" TCSlib TCSlib.lean | tar -x -C "$W/tipexport"
cmp "$W/tipexport/$REL" "$D/base/$REL"
{ echo "# names.py on the base (${BASE_REV:0:8})"
  python3 -I "$SC/names.py" "$D/base" "$D/base/$REL" "$D/tree/$REL" | san
  echo; echo "# names.py on the tip's tree (${tip:0:8}; git archive)"
  python3 -I "$SC/names.py" "$W/tipexport" "$D/base/$REL" "$D/tree/$REL" | san; } > "$LG/names.log"
[ "$(grep -c "^NAMES: PASS" "$LG/names.log")" = 2 ]
ok "names (22 new public names; none occurs, alone or after a dot, in the base or the tip's tree)"
python3 -I "$SC/hygiene.py" "$D/base/$REL" "$D/tree/$REL" > "$LG/widths-hygiene.log"
ok "widths (<= 100) and hygiene"
rm -rf "$W/lintroot"; mkdir -p "$W/lintroot/scripts" "$W/lintroot/$(dirname "$REL")"
cp "$D/base/scripts/style_lint.py" "$W/lintroot/scripts/"; cp "$D/tree/$REL" "$W/lintroot/$REL"
{ echo "## scripts/style_lint.py (the repository's, verbatim), base file"
  (cd "$D/base" && python3 -I scripts/style_lint.py "$REL" 2>&1)
  echo "## the same, landed file"
  (cd "$W/lintroot" && python3 -I scripts/style_lint.py "$REL" 2>&1); } > "$LG/lint.log"
ok "style_lint: 0 findings on the base and on the landed file"
python3 -I "$SC/appendix.py" "$D/base/$REL" "$D/tree/$REL" > "$W/appendix.md"
python3 -I -c 'import sys; a = open(sys.argv[1]).read(); p = open(sys.argv[2]).read(); sys.exit(0 if p.endswith(a) else 1)' \
  "$W/appendix.md" "$D/audits/diagonal-p1-statements-pack.md"
ok "the pack's appendices equal the declarations as landed (regenerated by appendix.py)"

# ---- 5. elaboration: standalone, axioms, cut checks with baselines ---------------------------
rm -rf "$W/cut" "$W/out"; mkdir -p "$W/cut" "$W/out"
cp "$D/tree/$REL" "$W/cut/Diagonal.check.lean"
python3 -I "$SC/axfile.py" "$D/tree/$REL" "$W/cut/Diagonal.axioms.lean" > /dev/null
python3 -I "$SC/cutcheck.py" "$D/base" "$D/tree" "$W/graph/chains.txt" "$W/cut" | san > "$LG/cutfiles.log"
elab() { bash "$ELAB" "$WT" "$OL" "$W/cut/$1.lean" > "$W/out/$1.out" 2>&1 \
  || { echo "elaboration of $1 exited nonzero"; san < "$W/out/$1.out" | head -40; exit 1; }; }
elab Diagonal.check
[ ! -s "$W/out/Diagonal.check.out" ] || { echo "standalone elaboration printed diagnostics"; exit 1; }
ok "the landed Diagonal.lean elaborates standalone against the snapshot, with no diagnostic"
elab Diagonal.axioms
python3 -I "$SC/axcheck.py" "$W/out/Diagonal.axioms.out" 24 > "$LG/axioms.log"
san < "$W/out/Diagonal.axioms.out" >> "$LG/axioms.log"
ok "axioms: all 24 public declarations within propext, Classical.choice, Quot.sound"
for i in "${IMPORTERS[@]}"; do elab "$i.base"; elab "$i.cut"; done
python3 -I "$SC/compare.py" "$W/out" "${IMPORTERS[@]}" > "$LG/cut.log"
for i in "${IMPORTERS[@]}"; do
  { echo; echo "### $i: cut-check output"; san < "$W/out/$i.cut.out"; } >> "$LG/cut.log"
done
ok "cut checks: the 5 direct importers elaborate against the landed text, diagnostics = baseline"

# ---- 6. negative controls ---------------------------------------------------------------------
bash "$SC/negctl.sh" "$S" "$D" "$OL" | san > "$LG/negative-controls.log"
[ "$(grep -c -- "— PASS" "$LG/negative-controls.log")" = 9 ] || { echo "negative controls"; exit 1; }
! grep -q -- "— FAIL" "$LG/negative-controls.log" || { echo "negative controls"; exit 1; }
ok "negative controls: every check fails on its broken input (9 controls)"

# ---- 7. copy-text screens, niced, one at a time ---------------------------------------------
bash "$SC/screens.sh" "$D" > /dev/null
{ echo "## Delta (screendelta.py, pairdiff.py, copied verbatim from <S>/tools; screen v3)"
  python3 -I "$SC/screendelta.py" "$LG/screen-before.txt" "$LG/screen-after.txt"
  python3 -I "$SC/pairdiff.py" "$LG/screen-after.txt" "$LG/screen-before.txt"; } > "$LG/screen-delta.log"
grep -q "new 0 (cross-file 0)" "$LG/screen-delta.log"
ok "copy-text screen v3: no new pair (before 16, after 16, all pre-existing in the clock files)"

# ---- 8. checksums -----------------------------------------------------------------------------
echo "TOTAL: $pass checks PASS" | tee -a "$LG/summary.log"
(cd "$D" && find tree patches scripts logs audits replay-order.txt LANDING-NOTES.md \
   BUNDLE-FILES.txt -type f \
   ! -name '*.pyc' | LC_ALL=C sort | xargs shasum -a 256) > "$D/SHA256SUMS"
echo "wrote SHA256SUMS"
