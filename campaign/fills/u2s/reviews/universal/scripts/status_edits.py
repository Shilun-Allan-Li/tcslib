"""Apply the drafted landing edits S1-S6 (public-facing status text and U2-E's Implementation
paragraph) in a worktree. Usage: status_edits.py <worktree>"""
import sys, os
wt = sys.argv[1]
def edit(path, pairs):
    p = os.path.join(wt, path)
    s = open(p, encoding='utf-8').read()
    for name, old, new in pairs:
        n = s.count(old)
        assert n == 1, (path, name, n)
        s = s.replace(old, new)
        print(path, name, 'applied')
    open(p, 'w', encoding='utf-8').write(s)
UK = 'TCSlib/Complexity/TuringMachine/UniversalK.lean'
edit(UK, [
("S1", """**Status.** The scheme interface and its two instances are defined and proved, and so is the
startup `Turing.exists_selfStartupTMK`; the other two machine contracts are sorried with their
proof sketches. Their fill builds on H2's step block and its forwarding round loop
`Turing.StepBlock.exists_forwardLoopTM` (H2-F, `Build/StepBlockForward.lean`).""",
"""**Status.** Proved: the scheme interface and its two instances, the startup
`Turing.exists_selfStartupTMK`, and both machine contracts. They are built on the step block's
forwarding round loop `Turing.StepBlock.exists_forwardLoopTM` (`Build/StepBlockForward.lean`)
and, for the code-first evaluator, on the ruler host `Turing.exists_rulerHostTM`
(`Build/InputDevice.lean`)."""),
("S2", """* `Turing.exists_selfUniversalK` — U2-U, the self-application universal machine, with time
  `C · (t + 1)`, space `C · (s + 1)` and the converse (sorried).
* `Turing.universalK` — U2-E, the code-first evaluator with time `C · (t + 1)` and the converse
  (sorried).""",
"""* `Turing.exists_selfUniversalK` — the self-application universal machine, with time
  `C · (t + 1)`, space `C · (s + 1)` and the converse (proved).
* `Turing.universalK` — the code-first evaluator with time `C · (t + 1)` and the converse
  (proved)."""),
("S3", """(the two cuts), so every completed output of `U` is `M`'s on `x`. -/
theorem universalK""",
"""(the two cuts), so every completed output of `U` is `M`'s on `x`.

**Implementation.** The steps of the sketch run in a different order. The startup
`Turing.exists_selfStartupTMK` runs first, on `pairEncode α x` (its endpoint does not depend on
`x`), embedded in the first `K + (k + 2)` of `K + (k + 3)` tapes. A finite-state scan then reads
the header from input position `1` in aligned pairs, marking one cell for each header cell on
tape `k + 2`, which the startup leaves blank, and stops at the separator with the input head at
`ℓ + 1`; the work-tape rewind `Turing.rewindTM` returns that tape's head to its first cell. After
`T + 2ℓ + 4` steps in all (seams included), the first `k + 3` tapes hold the ruler host's
presentation `Turing.rulerHostCfg` of the forwarding loop's encoding of `M`'s initial
configuration on `x`, with the ruler as the last of them and the initial tag `false` (virtual
input position `1`). From there the ruler host of `Turing.exists_rulerHostTM` runs the forwarding
loop of `Turing.StepBlock.exists_forwardLoopTM`. With `T` the startup's time, `D` the loop's
per-step bound `50 · (|tableBitsK| + 1) + C_L` and `C_R` the host's factor, the constant is
`C = T + 2ℓ + 5 + C_R (ℓ + 1) D`, which depends on `α` only. -/
theorem universalK"""),
("S4", """probe); re-deriving `Turing.universal` from it is the U-1 retrofit, deferred until this
statement is filled. At `k = 2` it is the core of Theorem 1.9 at `T log T` with the
Hennie–Stearns conversion (design note §4).""",
"""probe); re-deriving `Turing.universal` from it is deferred. At `k = 2` it is the core of
Theorem 1.9 at `T log T` with the Hennie–Stearns conversion (design note §4)."""),
])
edit('TCSlib/Complexity/TuringMachine.lean', [
("S5", """  evaluator. The startup is proved; the other two contracts are sorried.""",
"""  evaluator, all proved."""),
("S6b", """  Statement gate passed 2026-10-14; both are the `k = 1` cases of `UniversalK`'s statements.""",
"""  Both are proved, as the `k = 1` cases of `UniversalK`'s statements."""),
])
edit('TCSlib/Complexity/TuringMachine/SelfUniversal.lean', [
("S6a", """**Status: statement gate passed 2026-10-14** (round 1, 0/0/5;
`audits/b6-hosts-statements-findings.md`). Both statements are the `k = 1` cases of the
`k`-generic `Turing.exists_selfStartupTMK` and `Turing.exists_selfUniversalK`
(`TuringMachine/UniversalK.lean`, U2 statement gate pending; user decision (a), 2026-10-14), and
are proved from them here, with their statements unchanged; the construction, its sketch and its
fill are the generic ones.""",
"""**Status: proved.** Both statements are the `k = 1` cases of the `k`-generic
`Turing.exists_selfStartupTMK` and `Turing.exists_selfUniversalK`
(`TuringMachine/UniversalK.lean`), and are proved from them here, with their statements
unchanged; the construction, its sketch and its fill are the generic ones."""),
])
