# Levin padding (#286): production verification, 2026-11-11

**Status: all touched-declaration reads repaired (head `a1293a6970b4039a9cf19fd475b9f8cf304a44b3`); Gate 11 (Codex) staged.**

## Pins
- PR head `9ada398e06c00656f96207f5254a826c74130c15`, PR base `5bcf11aaf08963ab33ce608ea7509e7403e4351a`.
- Verified on a local trial merge `562ad0cacbc718ed3d932e509822cfa24087acfa` (parents `9ada398e…`, campaign
  `4a09f3993eb9344fc5714610e41ab141a0144db8`; never pushed). The 13 PR files are byte-identical to the PR head.
- Campaign later moved to `a3dcb21c` (records only, 0 Lean files).
- Evidence: `levin-production-verification.zip`, SHA-256
  `2c35f989332f6aa5d77a66b0f35f6b058943b1322f234784f0d4b4812115d63c`; its `SHA256SUMS` (1,669 files) is
  `evidence-SHA256SUMS` here, SHA-256 `a07afff2a771b8274601c33d80fd5a2072b789d90617fab824b45a587dcc9057`.
  Index: `DISPOSITIONS.txt`, `provenance.json`.

## Results
- **Bootstrap:** 1,195/1,195 modules (31 PFR copied by blob id + 1,164 merged closure, 375 Mathlib roots),
  0 errors, one fresh tree. `sorry` in the 13 files unchanged (3 in `TuringMachine/Build/Primitives`, 1 in
  `Universal`: `exists_canonizerExp`). An 87-module owner tree is byte-identical. Hand-off item 5 (reuse) is
  resolved by the fresh bootstrap; the Mac retained-reference probe is kept as superseded.
- **Generated helpers:** 24 of 26 changed helper names are gone; the remaining 2 are used only by
  `exists_emitIterTM`. No outside reference.
- **Statements (`decls2.py` vs 5bcf11aa):** 16 added, 5 removed (the `nu` block moved verbatim to
  `Parameter.lean`, plus reader `nu_eq`), 0 changed. No existing `def` body changed.
- **Axioms:** `exists_linearTime_gStr`, `lemma_64_3`, `theorem_63_1` use only `propext`, `Classical.choice`,
  `Quot.sound`. `sorryAx` only in 9 untouched Primitives theorems on 3 pre-existing sorries and in
  `exists_canonizerExp`.
- **Seals (full import-closure definitions, minus notation):** touched declarations clean except F1–F3; every
  untouched failure is identical at base; none touches the 52 approved provider pairs.
- **Controls:** 38 probes, 160/160 rows as expected.
- **Explicit-reader scan:** 531 foreign-definition items, none in a touched declaration.

## Findings (attribution confirmed by single-name unseal)
- **F1.** `Turing.FinTM.exists_emitIterTM_withFuel` (`TuringMachine/Build/EmitIterBody.lean`, new) destructures
  `Turing.SafeRun` (`Build/EmitIterEmbed.lean`) with `obtain ⟨hrun, hsafe⟩`. Moved from base
  `exists_emitIterTM`. Needs a published `SafeRun_iff` in `EmitIterEmbed.lean` (a file outside #286).
- **F2.** `PadQuad.linear_split` (`UniversalPadding/Machine.lean`, new private) proves `Linear split` from
  `computesFunInTime_pairSplitAt` by unfolding its compiler-generated matcher (`Randomized/Primitives.lean`, a
  file outside #286). Needs a named split function with case lemmas in `Randomized/Primitives.lean`.
- **F3.** `PadQuad.exists_family` (`UniversalPadding.lean`) changed only in its docstring; reads
  `FunFamily.ofString` identically at base; the reader `FunFamily.ofString_inLen_eval` exists. Ruling needed.

## Deviations
Primitives sealed in 3 segments (100-error cap); the two facade seals chunked at 1,000 names (stack); PFR copied
because symlinked sources are rejected. Failed attempts retained in the evidence.

## Repairs and re-verification (r2–r4)

Rulings (Seyoon, 2026-11-11): F1/F2 fixed inside #286 with `computesFunInTime_pairSplitAt`
restated; F3 counts as untouched. One maintainer commit `a1293a69` on
`codex/pass-shelat-levin-padding` holds the final repair (patch `fix-r4.patch`, SHA-256
`ef659c92688d8f437784544f195c74211d5d70be2f10edc0008a3938b6774edb`).

- **r2** (F1/F2 patch): replay 242/242 (a first attempt stopped at a wrong `body_round` edit,
  kept). F1, F2 cleared. New **F4**: the restated `computesFunInTime_pairSplitAt` still read
  PairSplit's private matcher through `exists_pairSplitTM` (as at base).
- **r3** (`pairSplitAt` moved into `Randomized/Build/PairSplit`): replay 244/244. F4 cleared. New
  **F5** (`exists_pairSplitTM` applied `ComputesFunInTime` as a function, as at base), **F6**
  (private `polyTimeComputable_pairSplitAt` newly read the moved definition), **F7**
  (`simp [MultiTapeTM.initCfg, Cfg.init]` in `split_computes`, touched by the restatement).
- **r4**: `exists_pairSplitTM` through `computesFunInTime_iff` (F5); the private lemma restated
  as `PolyTimeComputable pairSplitAt`, its users through `pairSplitAt_pairEncode` (F6);
  `split_computes` back at its base text, so F7 is an inherited untouched line. Replay 244/244.
  Seals: 0 touched failures in all changed files; untouched failures identical at base.
  Attribution clears F5/F6. Controls pass. Scan: no foreign-definition item in a touched
  declaration. Statements: CHANGED `exists_pairSplitTM`, `computesFunInTime_pairSplitAt`;
  ADDED 21; REMOVED the 5 moved `nu` declarations. 182 selected declarations, standard axioms.

Evidence r1–r4: `gates/11-levin/verification.zip`, SHA-256
`622fbc0bef25aad83e54c99fcd6b3f372456c3d8bd2841c8747c5e732b62367f` (r2 `8e89a4f0…`, r3
`1a67be51…` zips are subsets and stay local).
