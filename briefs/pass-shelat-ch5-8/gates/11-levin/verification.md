# Gate 11 verification

PR #286 head `a1293a6970b4039a9cf19fd475b9f8cf304a44b3` (Codex's production checkpoint
`9ada398e06c00656f96207f5254a826c74130c15` plus one maintainer repair commit), base
`5bcf11aaf08963ab33ce608ea7509e7403e4351a`. Sixteen Lean files change; their blobs are pinned in
[source-head.json](source-head.json). The campaign has since merged #284 and #285 at
`4a09f3993eb9344fc5714610e41ab141a0144db8`, which touches none of the sixteen files. All checks
below ran on a local trial merge of the PR into that campaign head, so they cover the merged
consumers too.

- **Fresh bootstrap (r1).** 1,195/1,195 modules in one fresh tree: 31 PFR sources (copied by git
  blob id) and the 1,164-module merged closure of the library root and campaign `Checks`, on
  375 narrowed Mathlib roots. 0 errors. No compiled object was reused. An 87-module owner tree is
  byte-identical to the full bootstrap. The Mac retained-reference probe is superseded by this
  bootstrap and kept.
- **Repair replays (r2–r4).** After each repair, every module downstream of the changed files was
  rechecked into the same tree: 242, 244 and 244 modules, all rc 0, 0 errors. The first r2 attempt
  stopped at an incorrect edit and is kept as superseded.
- **Generated helpers.** 24 of the 26 renamed helper names are gone; the other two are used only
  by `exists_emitIterTM`. No constant outside the PR's files references any of them.
- **Statements** (`decls2.py` against the base, all 16 files): CHANGED exactly
  `Turing.FinTM.exists_pairSplitTM` and `Turing.FinTM.computesFunInTime_pairSplitAt` (both
  restated against the new `Turing.pairSplitAt`, same proposition); ADDED 21; REMOVED the five
  `nu` declarations, moved verbatim to `UniversalPadding/Parameter.lean` with the reader `nu_eq`.
  `exists_linearTime_gStr` keeps its original header. No existing definition body changed.
- **Axioms.** 182 selected new or changed declarations use only `propext`, `Classical.choice` and
  `Quot.sound`, including `exists_linearTime_gStr`, `lemma_64_3` and `theorem_63_1`. In the ten
  non-facade owners `sorryAx` occurs only in nine untouched `TuringMachine/Build/Primitives`
  theorems resting on its three pre-existing admissions, and in `exists_canonizerExp` (the
  separate canonizer task).
- **Seals.** Every changed file was sealed whole, installing every definition of its full
  TCSlib import closure (abbreviations and `PolyExpr.eval` excepted), with the archived
  instrumenter. `TuringMachine/Build/Primitives` was sealed in three segments (Lean's 100-error
  cap) and the two facades in 1,000-name chunks (stack). Rounds r1–r4 found reads in touched
  declarations F1, F2, F4, F5, F6; the repair commit fixes all of them (see
  [the verification records](../../maintainer/levin-production-2026-11-11/README.md)). At the head,
  **no touched declaration fails**. Every untouched failure is identical at the base control.
  None of them is among the 52 approved provider pairs.
- **Controls.** r1: 38 probes, 160/160 rows as expected; r2–r4: 16 further probes for the newly
  touched files. Old-style reads pass unsealed and fail sealed with exactly one error; the
  published readers pass sealed.
- **Explicit-reader scan.** No foreign-definition item in a touched declaration. Inherited items
  sit in untouched declarations of `TuringMachine/Build/Primitives`, `EmitIterBody`,
  `EmitIterEmbed` and `Randomized/Build/PairSplit`.
- **Rulings applied.** Provider reuse (52 pairs, 2026-11-10). F1/F2 fixed inside #286 with
  `computesFunInTime_pairSplitAt` restated (2026-11-11). F3: a docstring-only change counts as
  untouched; `PadQuad.exists_family`'s read of `FunFamily.ofString`, identical at base, joins the
  inherited failures. F7 was avoided by keeping `split_computes` at its base text.
- **Lint.** No new `sorry`. The repairs add no line over 100 characters. The original PR has 15
  module-docstring lines over 100 characters; the campaign lint does not check line length.

[Verification archive r1–r4](verification.zip) (SHA-256
`622fbc0bef25aad83e54c99fcd6b3f372456c3d8bd2841c8747c5e732b62367f`; its `final/SHA256SUMS`
covers 2,679 files and is indexed by the `DISPOSITIONS*.txt` files).
[362-module source closure at the head](sources.zip) (SHA-256
`cf96a5ba6e886760abc871743699311929720fd5397fde61eb2c2fb228cfc4a9`).

**Post-audit note (Gate 11 N1).** The trial-merge build includes one campaign file that differs from
the PR head's closure: `Foundations/Negligible.lean`, which gained `Negligible.comp_of_le` through
#284 (merged at `4a09f399`). The padding proof does not use it.
