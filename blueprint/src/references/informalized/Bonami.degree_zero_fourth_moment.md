<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Bonami.lean :: degree_zero_fourth_moment -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Degree-zero functions satisfy the fourth-moment bound with equality

**Claim.** If `f : BooleanFunc n` has `has_degree_at_most f 0`, then
`expect (fun x => f x ^ 4) = (expect (fun x => f x ^ 2)) ^ 2`, where
`expect g = 2⁻ⁿ · ∑_{x} g x`.

**Proof.**

1. `have h_const : ∀ x, f x = f default` from `degree_zero_const f hf`.
2. Unfold `expect` and rewrite every occurrence of `f x` to `f default`
   (`simp [h_const]`); both sides are now constants times powers of `2⁻ⁿ` and
   `Finset.card_univ = 2 ^ n`.
3. The remaining identity is bookkeeping on the normalisation factor:
   `unfold uniformWeight`, `norm_num [pow_mul]`, `ring_nf`, then
   `simp [pow_mul']` — the point being `(2⁻ⁿ · 2ⁿ · c²)² = 2⁻ⁿ · 2ⁿ · c⁴`, both
   sides collapsing to `f default ^ 4`. ∎

**Remark.** This is the `k = 0` case of `bonami_expect`, where `9 ^ 0 = 1` makes
the Bonami inequality an equality; it is consumed there via `le_of_eq`.
