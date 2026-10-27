"""Optional landing edits E1-E4 for checkpoint 1 (python3 -I); every replacement is asserted unique.
usage: python3 -I landing_edits.py <NTimeDiagonalizer.lean>"""
import sys
p = sys.argv[1]; s = open(p, encoding='utf-8').read()
E = [
 # E1: qy_guard's docstring claimed agreement "exactly" on long unary words; words of length at most
 # two agree too (both sides are empty).
 ("/-- The query agrees with its unary-input version exactly on unary words of length at least\nthree, and is empty otherwise. -/",
  "/-- The query of a word is the query of the unary word of the same length when the word is unary\nof length at least three, and is empty otherwise. -/"),
 # E2: the leaf's docstring says which public row it is not (the brief's leaf rule).
 ("no input scan beyond those rows.\n\n**Proof sketch.** Fixed-width",
  "no input scan beyond those rows. No public row decides this guard: the fixed-word test\n`Turing.FinTM.computesFunInTime_ifEq` decides one word, and the increment\n`Turing.FinTM.computesFunInTime_incFixed` signals an all-true word only by an empty output.\n\n**Proof sketch.** Fixed-width"),
 # E3: close the singleton congruence without reducing the core `List.singleton`.
 ("  apply congrArg List.singleton\n", "  refine congrArg (fun b => [b]) ?_\n"),
 # E4: one blank line, not two, before the target's docstring.
 ("    _ = _ := by ring\n\n\n/-- **The stage query in linear time**", "    _ = _ := by ring\n\n/-- **The stage query in linear time**"),
 # E5: the status paragraph names the frozen sketch's last obligation, the ledger, as open.
 ("query on the unary word of every input's length are proved. The setup, capped locator, stage-code\nconversion, budget computation and output writer remain open. -/",
  "query on the unary word of every input's length are proved. The setup, capped locator, stage-code\nconversion, budget computation, output writer and linear ledger remain open. -/"),
]
for old, new in E:
    assert s.count(old) == 1, old[:60]
    s = s.replace(old, new)
open(p, 'w', encoding='utf-8').write(s); print('applied', len(E), 'edits')
