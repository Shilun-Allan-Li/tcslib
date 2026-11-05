# Gate 02: pack errata

The pack is shipped and is not edited; corrections are recorded here and carried into round 2.

| # | Pack location | Erratum | Found |
|---|---|---|---|
| E1 | Scope, context | The inventory row of Thm 175.1 (`inventory-ch5-8.md`), which already recorded the expected-polynomial-time debt (finding 4), was not in the bundle. Round 2 includes the inventory rows of the source items it asks about. | 2026-11-05, review sub-agent |
| E2 | Attestation 4 ("No ch. 2–4 module is imported") | True at round 1's head. After the round-1 repairs, `Games/Advantage.lean` imports `TCSlib.Cryptography.Foundations.Probability` (finding 10, ruled: reuse `abs_sub_le_sum_hybrids` and `exists_hybrid_gap`); that module imports only Mathlib. | 2026-11-05, maintainer |
| E3 | Attestation 6 (generalizations disclosed) | `advantage_hybrid` was a statement-level duplicate of `abs_sub_le_sum_hybrids`, not disclosed (finding 10). Resolved by reuse. | 2026-11-05, auditor |
| E4 | Round 2 pack, attestation 2 ("all 75 theorems") | All 75 *public* theorems were printed. The private helper `expect_ite_one_split` has no separate print; it is covered transitively. The closing evidence says so. | 2026-11-05, round 2 auditor (note 6) |
