<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Bonami.lean :: degree_avgLast -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Averaging out the last coordinate does not raise the degree

**Claim.** For `f : BooleanFunc (n+1)` and `k : ℕ`, if `has_degree_at_most f k`
then `has_degree_at_most (avgLast f) k`, where
`avgLast f x = (f (snoc x false) + f (snoc x true)) / 2`. Degree is the
Fourier notion `has_degree_at_most f k : ∀ S, f̂(S) ≠ 0 → S.card ≤ k`.

**Proof.**

1. Fix `S : Finset (Fin n)` with `fourierCoeff (avgLast f) S ≠ 0` (`intro S hS_nonzero`).
2. An inline `have h_fourier_coeff` re-derives the transfer identity
   `fourierCoeff (avgLast f) S = fourierCoeff f (S.image Fin.castSucc)`:
   unfold `fourierCoeff`, `avgLast`, `innerProduct`, `restrictLast`, `expect`,
   split the sum over `BoolCube (n+1)` with `sum_boolCube_succ`, and use
   `Finset.prod_image` on `chiS` plus `uniformWeight` arithmetic (`ring_nf`).
   The point is that `χ_{S.image castSucc}` ignores the last coordinate, so it
   takes the same value on `snoc x false` and `snoc x true`; the two halves of
   the split sum recombine into the average.
3. Instantiate the hypothesis at the lifted set: `have := hf (S.image Fin.castSucc)`.
4. `Fin.castSucc` is injective, so `Finset.card_image_of_injective` gives
   `(S.image Fin.castSucc).card = S.card`, and `simp_all` closes `S.card ≤ k`. ∎

**Remark.** The `have` in step 2 duplicates the standalone lemma
`fourierCoeff_avgLast` proved earlier in the same file; the lemma is not
invoked here.

**Used in.** `bonami_expect` (inductive step: `hg_deg`), paired with
`degree_diffLast`.
