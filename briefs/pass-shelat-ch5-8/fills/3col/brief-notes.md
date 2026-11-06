# Notes for the 3-colouring fill brief (not yet drafted)

Targets: the three admissions of pack 03g, `R3COL_witnessRelation` (its `decidable` clause),
`colRep_efficientProverProof` and `col_zk`. They are issued after gate 03g closes.

From the gate 03g review (`gates/03-ch2-4/review/gate03g-review.md`):
- `col_zk` follows the corrected sketch (review §2.3). The leading term is `N²·ε_B(⌊√N⌋)`. The
  bridge from ideal coins to a machine fixes the attempt table with
  `CommitmentLemmas.exists_fixCoins`, as `Commitment.multiHiding` does, so the hiding machine makes
  one verifier call and one call to `D`. The `m = 0` case needs `n ≥ 1`, and `N = 0` is bounded
  by 1.
- The ladder (review M3):
  1. `statClose_sampleColorPair` (within `(1/4)^T` of uniform on `ColorPair`);
  2. the real view to `some ∘ colRealView`;
  3. `colSim` to `colSimTrunc`;
  4. `exists_colSimRed_fixCoins`;
  5. the reduction machine `exists_colHidingRed`;
  6. the `m = 0` reduction;
  7. the assembly.
- The fill also sweeps the 20 pre-existing lint findings of the 3-colouring files (decision of
  2026-11-05).
- Optional: move `Negligible.comp_sqrt` next to `negligible_exp_neg_sqrt_div` (review M4).
