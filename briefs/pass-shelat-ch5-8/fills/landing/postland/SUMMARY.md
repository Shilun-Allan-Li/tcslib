# Post-landing verification of the merged base (2026-11-07)

Base `aa276ae809d7f64c9f10eae7decfc635db4d1c98` (records branch after #210, #224, #225, #226), compared with `a3cca8ab0c456088132501a57eb751bccdf98ef5`
(#210 merged, before the landings). Checked by an internal verification agent; logs in this folder.

- **Replay:** 109 TCSlib modules, namely the 17 changed files (14 from the landings and 3 docstring
  files) and everything downstream of them, then `audits/pass-shelat/Checks`. Each was checked alone
  with `scripts/lean_check_tree.sh`. **0 errors** (`replay.log`).
- **`sorry` census** of `TCSlib/Cryptography` (executable tokens): **65 → 2**, a drop of exactly 63.
  - Per file: Concrete 1, DiscreteLog 6, DiscreteLogHardcore 7, ElGamal 7, Factoring 10, RSA 10,
    Rabin 19, Protocol 2, Simulator 1.
  - The 2 left are outside the fills: `exists_canonizerExp` (`Universal.lean`) and
    `PadQuad.exists_linearTime_gStr` (`UniversalPadding.lean`).
- **Axioms:** all 27 fill targets and headlines print exactly `[propext, Classical.choice, Quot.sound]`
  (`axioms.log`).
  - The sweep covered 2946 constants (1361 public) in the 7 Candidates files, the 13 ThreeColoring
    modules and `NP`. None depends on `sorryAx`.
  - The control run on Universal/UniversalPadding flags 5 constants, so the sweep detects
    `sorryAx` (`axioms-control.log`).
- **`Checks`:** 364 records. 53 became standard-axiom-only and none got worse; `sorryAx` records went
  from 57 to 4. The 4 left are `NUPPT.decides_of_decidesWithAdviceInTime`, `lemma_64_3`,
  `theorem_63_1` and `exists_canonizerExp`, none of them from the fills (`checks-diff.txt`).
- **Lint:** only the approved size lines. The 9 facade FAILs are the base's; 8 "sorry without proof
  sketch" FAILs are gone.
