# Levin padding (#286): production verification, 2026-11-11

**Status: three touched-declaration reads (F1–F3) open; the Codex audit (Gate 11) waits on them.**

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
