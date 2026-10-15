"""Derive the landing's log runner (scripts/logs.sh) from the gate's scripts/runall.sh by asserted
replacements: the base is the campaign tip's export, the snapshot oleans-lmain, the output folder
land-g24. Usage: python3 -I derive_logs.py <gate runall.sh> <out logs.sh>"""
import sys
src, dst = sys.argv[1:3]
t = open(src, encoding="utf-8").read()
def rep(a, b, n=1):
    global t
    c = t.count(a)
    assert c == n, (a[:70], c)
    t = t.replace(a, b)
rep("""# Re-run every check of the §13d G2–G4 statement gate (rebuild at the tip) and write the logs.
# Read-only: `lean` only through tools/leanelab.sh (no -o, no olean written), python3 -I only,
# read-only git (`rev-parse`, `diff --name-only`; the base tree is a `git archive` export).
# Usage: bash runall.sh <S>
#   base tree  <OUT>/base  = `git archive f2d48ad5` (Lean content = 1b6b972c), its .lake a symlink to
#              the packages of <S>/wt-g24 (same lake-manifest); snapshot <S>/oleans-lb6.
S="$1"; O="$S/gate-g24"; WT="$O/base"; GW="$S/wt-g24"; REV=f2d48ad5; OL="$S/oleans-lb6"
""", """# The §13d G2–G4 LANDING (gate closed 2026-10-14): rebuild the landed files at the campaign tip and
# re-run the gate's checks there (derived from the gate's runall.sh by scripts/derive_logs.py).
# Read-only: `lean` only through tools/leanelab.sh (no -o, no olean written), python3 -I only; the
# base tree is a `git archive` export of the tip. Usage: bash logs.sh <S>
#   base tree  <OUT>/work/base = `git archive <tip>` (work/base-commit.txt), its .lake a symlink to the
#              packages of <S>/wt-mig1tip (same lake-manifest); snapshot <S>/oleans-lmain (the root replay).
S="$1"; O="$S/land-g24"; WT="$O/work/base"; GW="$O/work/base"; REV=$(cat "$O/work/base-commit.txt"); OL="$S/oleans-lmain"
""")
rep('''HDR="Tool: \\`bash <S>/tools/leanelab.sh <OUT>/base <S>/oleans-lb6 <file>\\` (direct \\`lean\\`, no \\`-o\\`, no olean
written). Base: <OUT>/base, a read-only \\`git archive\\` export of $(git -C "$GW" rev-parse --short $REV) (the local
\\`origin/complexity/arora-barak-ch3-4\\`; its Lean files equal 1b6b972c's: PRs #92 and #93 merged); its \\`.lake\\` is
a symlink to <S>/wt-g24's packages (same \\`lake-manifest.json\\`). Snapshot: \\`oleans-lb6\\`. Toolchain:
\\`$(cat "$WT/lean-toolchain")\\`. <OUT> is the gate's output directory; <S> the scratchpad. Run: $(date -u '+%Y-%m-%d %H:%M UTC')."''',
'''HDR="Tool: \\`bash <S>/tools/leanelab.sh <OUT>/work/base <S>/oleans-lmain <file>\\` (direct \\`lean\\`, no \\`-o\\`, no
olean written). Base: <OUT>/work/base, a read-only \\`git archive\\` export of the campaign tip ${REV:0:8} (after #105,
the merge to main); its \\`.lake\\` is a symlink to <S>/wt-mig1tip's packages (same \\`lake-manifest.json\\`). Snapshot:
\\`oleans-lmain\\` (the root replay at ff2d6f6b, Lean-equal to the tip). Toolchain: \\`$(cat "$WT/lean-toolchain")\\`.
<OUT> is the landing folder; <S> the scratchpad. Run: $(date -u '+%Y-%m-%d %H:%M UTC')."''')
rep('''echo "Against every declaration of the base tree (PRs #92 and #93 merged), and the pending statement units"
echo "of the base: MIG-1, the C1 assembly, the H1 harvest, the B5a canonizer overlay, RD-2 and stage 2."''',
'''echo "Against every declaration of the tip tree, the statement units of the earlier gates (MIG-1, the C1"
echo "assembly, the H1 harvest, the B5a canonizer overlay, RD-2, stage 2) and the pending B5a canonizer"
echo "continuation 4 overlay (its fill is out)."''')
rep('''  "$WT/audits/evidence/stage2-gate/LanguageExtensions.lean.txt" 2>&1 | san''',
'''  "$WT/audits/evidence/stage2-gate/LanguageExtensions.lean.txt" \\
  "$WT/audits/evidence/b5a-canon-cont4/CanonCont4Overlay.lean.txt" 2>&1 | san''')
rep('''echo "## 4. The facade (\\`mkfacade.py\\`), rebased on PR #92's additions"''',
'''echo "## 4. The facade (\\`mkfacade.py\\`), at the tip"''')
rep('''echo "<OUT>/work/superseded-r0/ (built at 759471be with oleans-lm0b)."''',
'''echo "gate-g24 folder (built at f2d48ad5 with oleans-lb6); this landing rebuilds them at the tip."''')
rep('''echo "campaign checkout after the run:"
echo '```'; git -C "$GW" status --short | head; echo "(end)"; echo '```\'''',
'''echo "base export after the run (it is read-only; compared with the tip's tree by verify.py):"
echo '```'; echo "(the base is not a checkout; see verify.py's precheck)"; echo '```\'''')
rep('echo "checkout (<S>/wt-g24, records) that mention it."',
    'echo "tip export (<OUT>/work/base, records included) that mention it."')
open(dst, "w", encoding="utf-8").write(t)
print("derived", dst)
