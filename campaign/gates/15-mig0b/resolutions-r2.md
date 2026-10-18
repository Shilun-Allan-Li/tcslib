# MIG-0b gate, round 2: resolutions

**Round 2:** `audits/mig0b-r2-pack.md`; bundle `audits/mig0b-r2-bundle.md`, SHA-256
`3e697e9e588fe1eca2669de01b1c47c5c61cc7af8a816095f18fbde9fa9559fb`, 72 sections.
**Findings:** `audits/mig0b-r2-findings.md`, verbatim.
**Verdict: CLOSED (2026-10-14): 0 blockers, 0 majors, 3 minors.** Both round-1 majors are resolved.
The landing PR's own replay remains an obligation.

| # | Finding (short) | Resolution |
|---|---|---|
| 1 | The landing-unit size omits the `TuringMachine.lean` facade's change: 17 files, net +2,084 | Accepted; the backlog's MIG-0 measurement is corrected (about 3.2k in total, unchanged). |
| 2 | `identity.py`'s status-paragraph assertion is vacuously true | Accepted. The landing PR compares the landed `Build/Contract.lean` and the new facade by full-file diff, after replacing exactly the status paragraph. The evidence scripts are not acceptance gates. |
| 3 | `Contract.lockstep`'s docstrings call entry compatibility for every source configuration necessary | **At landing:** a sufficient-condition formulation; compatibility on admissible source starts also suffices. No theorem changes. |

**Rulings on the open questions:**
1. Part 7, the admitted alphabet pair, lands with RS-5, when its proof is supplied. The landing PR
   withholds part 7 and regenerates the landing set, documentation, closures and the axiom and
   signature checks for that variant.
2. The universe generalizations are accepted; the guarded-renaming move stays verbatim.
3. `Finite`, not `Deterministic`.
4. The extended cut check is limited pre-landing evidence, not a rebuild; the landing replay
   stays.
5. Landing order around `CodeSimulator.lean` as recommended: the one-token edit at `:5841` goes in
   an ownership window, after H2-M, with probe 109 and its negative twin re-run.
