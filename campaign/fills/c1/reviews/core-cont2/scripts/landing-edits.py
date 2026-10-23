"""The maintainer's drafted landing edits (docstrings only), every edit asserted to match exactly once.
usage: python3 -I landing-edits.py <worktree> [with-implementation 0|1]"""
import sys, os
wt = sys.argv[1]; impl = len(sys.argv) > 2 and sys.argv[2] == '1'
def edit(rel, pairs):
    p = os.path.join(wt, rel); t = open(p, encoding='utf-8').read()
    for a, b in pairs:
        n = t.count(a); assert n == 1, f'{rel}: {n} occurrences of {a[:60]!r}'
        t = t.replace(a, b)
    open(p, 'w', encoding='utf-8').write(t); print(f'{rel}: {len(pairs)} edit(s)')
nd = [("* `Turing.exists_ndInterpreterCore` — the interpreter core `R` (sorried).",
       "* `Turing.exists_ndInterpreterCore` — the interpreter core `R` (proved, modulo the canonizer).")]
if impl:
    nd.append(("""(`Turing.NDTM.runWith_initCfg_take`) with the branch on `x`. -/
theorem exists_ndInterpreterCore""",
"""(`Turing.NDTM.runWith_initCfg_take`) with the branch on `x`.

**Implementation.** `R` is one left-nested seam composite of twelve phases: the header pass
capturing `bits t`, an input rewind, the header pass capturing `α`, the rewind and the copy of the
counter (`Turing.rewindTM`, `Turing.copyTM`), the window copy, a second input rewind, the rewind of
`α`, the installation behind a release adapter, the seam layout (`Turing.exists_seamLayoutTM`), the
rewind of the window, and the hosted loop, embedded silently. The window is copied before the
installation, whose seam fixes the input head at its first cell. Each join is
`Turing.seamCompTM_run_ofCfg` with its inherited first-return cut. -/
theorem exists_ndInterpreterCore"""))
edit('TCSlib/Complexity/TuringMachine/NDCodeSimulator.lean', nd)
edit('TCSlib/Complexity/TuringMachine.lean', [(
"""  bridge, the per-code replay canonizer and the core `R` [AB09, Exercise 2.6]. The canonizer
  and the core are sorried.""",
"""  bridge, the per-code replay canonizer and the core `R` [AB09, Exercise 2.6]. The core is
  proved; the canonizer is sorried.""")])
