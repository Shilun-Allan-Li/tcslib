<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/DecisionTreeFourier.lean :: size_le_two_pow_depth -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# A depth-`k` tree has at most `2^k` leaves

**Claim.** For every `T : DecisionTree n`, `T.size ≤ 2 ^ T.depth`, an inequality
in `ℕ` between the leaf count and two to the depth.

**Proof.** `induction T`.

1. **Leaf `b`.** `simp [size, DecisionTree.depth]`: `1 ≤ 2 ^ 0`.
2. **Branch `i lo hi`.** Two monotonicity facts, `hlo` and `hhi`, raise each
   subtree bound to the common exponent: `2 ^ lo.depth ≤ 2 ^ max lo.depth
   hi.depth` and likewise for `hi`, both by `Nat.pow_le_pow_right` with
   `le_max_left` / `le_max_right` (and `by norm_num` for `1 ≤ 2`).
3. After `simp only [size, DecisionTree.depth]` a `calc` chain gives
   `lo.size + hi.size ≤ 2 ^ m + 2 ^ m` by `omega` from the inductive hypotheses
   and `hlo`/`hhi`, where `m = max lo.depth hi.depth`; then
   `rw [Nat.add_comm 1, Nat.pow_succ]` and `ring` identify
   `2 ^ m + 2 ^ m = 2 ^ (1 + m)`, which is `(.branch i lo hi).depth`.

**Used in.** `sparsity_le_four_pow`, which composes `sparsity_le` (support size
`≤ size · 2^depth`) with this bound to get the size-free form `≤ 4 ^ depth`.
