# W1 census: admissions and statements (2026-11-16)

Campaign at #325 (`20394834`, snapshot `oleans-c2039`); `main` at `dead9dc8`; their common base `abd2bd3d` (#179).

## Admissions

`CensusAll.lean.txt` imports all 876 modules of the snapshot and lists every `TCSlib` constant whose type or value uses
`sorryAx` directly (`CensusAll.out.txt`, exit 0): **76,454 constants, 166 direct admissions** in 32 modules.
`census-classify.txt` compares each module's source `sorry` count on the campaign, on `main` and at the base:

- **The campaign has introduced no admission since the last integration.** Every module's campaign count equals its base
  count; everything the campaign proved since (Ladner and the rest) is admission-free.
- 41 are the RD-2/H6 route (`ClassPSPACE/TQBF` 21, `FormulaKit` 20), ruled for removal (closeout D1, W2). They are also
  on `main`.
- The other 125 are in areas outside the campaign (BooleanAnalysis, Programs/WordRAM, RAMSimulation, ErrorCorrectingCodes,
  `Build/RecordTable`, `Expanders/Chernoff`), inherited from `main`. `main` has since closed one in GaussianSpace `Borell`
  and two in `SurfaceExamples`; the `main` sync (W4) brings those in.

## Public statements since the last integration

`statement-census.json`, over the 199 TCSlib files the campaign changed since the base (10 new): **326 public declarations
added, 26 removed, 19 restated.** `integration-risk.json` checks each removal and restatement:

- 16 of the 26 removals are moves (the name now lives in another file, mostly the shared `TuringMachine/NatBits` and
  `SpaceComplexity/Basic`); the other 10 are deliberate retirements (the Catalog sibling `*_run` rows, `runFrom_one`,
  `Action.apply_workTapes`) from gated dedup PRs.
- The 19 restatements are the Codec machine labels (15), `FinTM.toCodeTM`, and three Oblivious lemmas (gate 133).
- Files unchanged by the campaign compile against these in the full replay. `main`'s own 44 changed files mention none of
  the 45 names (`0 hits`), so integrating should break nothing; the W4 replay confirms it.
