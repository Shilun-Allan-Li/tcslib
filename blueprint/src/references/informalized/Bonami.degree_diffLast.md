<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Bonami.lean :: degree_diffLast -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The last-coordinate difference drops the degree by one

**Claim.** For `f : BooleanFunc (n+1)` and `k : ℕ`, if `has_degree_at_most f k`
then `has_degree_at_most (diffLast f) (k - 1)`, where
`diffLast f x = (f (snoc x false) - f (snoc x true)) / 2` and `k - 1` is
truncated subtraction on `ℕ`.

**Proof.**

1. An inline `have h_fourier_coeff` proves, for every `S : Finset (Fin n)`,
   `fourierCoeff (diffLast f) S = fourierCoeff f (S.image Fin.castSucc ∪ {Fin.last n})`.
   It rewrites `Finset.univ : Finset (BoolCube (n+1))` as the union of the two
   `Fin.snoc · false` / `Fin.snoc · true` images (disjoint by
   `Finset.disjoint_left`, injective by `congrArg Fin.init`), then evaluates
   `chiS` with `Finset.prod_union` / `Finset.prod_image` and
   `uniformWeight_succ`. The extra factor `boolToSign (x (last n))` is what
   turns the average into the half-difference.
2. Fix `S` with `fourierCoeff (diffLast f) S ≠ 0` (`intro S hS_nonzero`).
3. `have h_card : S.card + 1 ≤ k` — instantiate `hf` at
   `S.image Fin.castSucc ∪ {Fin.last n}`, whose cardinality is `S.card + 1`
   (`Finset.card_image_of_injective`, `Fin.last n` not in the image).
4. Conclude with `Nat.le_sub_one_of_lt`. ∎

**Remark.** Duplicates the standalone `fourierCoeff_diffLast` (same proof
script) rather than calling it. For `k = 0` the claim is still sound: step 3
then derives a contradiction, since every frequency of `diffLast f` has
cardinality at least one.

**Used in.** `bonami_expect` (inductive step: `hh_deg`).
