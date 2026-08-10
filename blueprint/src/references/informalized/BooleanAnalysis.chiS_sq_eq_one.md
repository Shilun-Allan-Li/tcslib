<!-- generated-by: proofmatch informalization (not_in_text) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Basic.lean :: chiS_sq_eq_one -->
<!-- origin: boolean-ch01-fourier-blr run cdca27e1b5fd verdict not_in_text (0.62) -->

# Walsh characters square to one

**Claim.** For every frequency `S : Finset (Fin n)` and every point
`x : BoolCube n`, `χ_[S] x ^ 2 = 1`. Equivalently, each character takes values
in `{-1, 1}`.

**Proof.** Unfold `chiS` (`simp only [chiS]`), leaving
`(∏ i ∈ S, boolToSign (x i)) ^ 2 = 1`, then induct on `S`
(`Finset.induction`).

1. Empty case: the empty product is `1` and `1 ^ 2 = 1` (`simp`).
2. Insert case: `Finset.prod_insert ha` splits off the new factor, `mul_pow`
   distributes the square over the product, `boolToSign_sq` rewrites the new
   factor's square to `1`, and `one_mul` discards it.
3. What remains is exactly the induction hypothesis `ih`.

**Remark.** A granular ±1-valuedness lemma; it is the fact that lets squares of
characters cancel, e.g. in `influence_chi` and in
`BooleanAnalysis/BLR/BoolFourier.lean` (`char_S_sq`).
