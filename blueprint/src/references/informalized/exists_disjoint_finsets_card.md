<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/QuantumSingleton.lean :: exists_disjoint_finsets_card -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Two disjoint coordinate sets of size `t` exist when `2t ≤ n`

**Claim.** For `t : ℕ` with `2 * t ≤ n`, there exist `A B : Finset (Fin n)` with
`Disjoint A B`, `A.card = t` and `B.card = t`.

**Proof.** Carve `A` out of `univ`, then `B` out of the leftover.

1. Put `U := Finset.univ`, so `U.card = n` (`simp`), and rewrite the hypothesis as
   `t + t ≤ U.card` (`two_mul`); in particular `t ≤ U.card`
   (`Nat.le_add_left`, `le_trans`).
2. `Finset.exists_subset_card_eq` yields `A ⊆ U` with `A.card = t`.
3. `(U \ A).card = U.card - A.card` from `Finset.card_sdiff` together with
   `Finset.inter_eq_left.2 hA_sub`.
4. Hence `t ≤ (U \ A).card`, since `t ≤ U.card - t` (`Nat.le_sub_iff_add_le`
   applied to step 1).
5. `Finset.exists_subset_card_eq` again yields `B ⊆ U \ A` with `B.card = t`.
6. `A` and `B` are disjoint: any `x ∈ B` lies in `U \ A`, so `x ∉ A`
   (`Finset.disjoint_left`, `Finset.mem_sdiff`).

**Used in.** `quantum_singleton_bound`, at `t = d' = code_dist S - 1`: the two
disjoint sets become two erasure patterns of size `d - 1`, each correctable by
`dist_implies_correctable`, which is what the cleaning bound consumes.
