<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Cube/Decomposition.lean :: degree_diffLast -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The last-coordinate difference drops the degree by one

**Claim.** For `f : BooleanFunc (n+1)` and `k : ℕ`, if `has_degree_at_most f k`
then `has_degree_at_most (diffLast f) (k - 1)`, where
`diffLast f x = (f (snoc x false) - f (snoc x true)) / 2` and `k - 1` is
truncated subtraction on `ℕ`.

**Proof.**

1. Introduce `have h_fourier_coeff`, asserting, for every `S : Finset (Fin n)`,
   `fourierCoeff (diffLast f) S = fourierCoeff f (S.image Fin.castSucc ∪ {Fin.last n})`.
   This is supplied directly by `exact fourierCoeff_diffLast f`.
2. Fix `S` with `fourierCoeff (diffLast f) S ≠ 0` (`intro S hS_nonzero`).
3. `have h_card : S.card + 1 ≤ k` — instantiate `hf` at
   `S.image Fin.castSucc ∪ {Fin.last n}`, whose cardinality is `S.card + 1`
   (`Finset.card_image_of_injective`, `Fin.last n` not in the image).
4. Conclude with `Nat.le_sub_one_of_lt`. ∎

**Remark.** The proof reuses `fourierCoeff_diffLast`. For `k = 0`, any nonzero
coefficient of `diffLast f` would give `S.card + 1 ≤ 0` in step 3, which is
impossible. Thus all Fourier coefficients of the half-difference vanish.

**Used in.** `BooleanAnalysis.Hypercontractivity.bonami_expect` in `TCSlib/BooleanAnalysis/Hypercontractivity/Cube/Bonami.lean`.
