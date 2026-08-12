<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Basic.lean :: fourierCoeff_odd_even -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Odd functions have no even-level Fourier weight

**Claim.** If `f : BooleanFunc n` is odd (`isOddFunc f`, i.e. `f(¬x) = -f(x)` for
all `x`) and `S : Finset (Fin n)` has even cardinality, then
`fourierCoeff f S = 0`.

**Proof.**

1. `simp only [fourierCoeff, innerProduct, expect, uniformWeight]` unfolds the
   coefficient, and `suffices h : ∑ x, f x * chiS S x = 0` discards the `2⁻ⁿ`
   normalisation (`simp [h]` finishes from the unnormalised sum) — only the bare
   sum needs work.
2. Build the antipodal map as an `Equiv` on `BoolCube n`: `e` has both `toFun`
   and `invFun` equal to `fun x i => !x i`, with `left_inv` and `right_inv` each
   by `ext; simp` (double negation). It is its own inverse.
3. `hcv` — change of variables. `Fintype.sum_equiv e _ _ (fun _ => rfl)`, taken
   `.symm`, gives `∑_x f(x) χ_S(x) = ∑_x f(¬x) χ_S(¬x)`: reindexing along a
   bijection of a finite type leaves the sum unchanged, and the summands match
   by `rfl`.
4. `hflip` — evaluate the flipped sum. `hodd'` supplies `f(¬x) = -f(x)` and
   `chiS_neg` supplies `χ_S(¬x) = (-1)^{|S|} χ_S(x)`. The sign is then killed by
   `hone : (-1 : ℝ) ^ S.card = 1`, proved from `heven` as `⟨k, hk⟩` via
   `rw [hk, ← two_mul, pow_mul]` with `(-1)^2 = 1` (`norm_num`) and `one_pow`.
   With `simp_rw [hodd', chiS_neg, hone, one_mul, neg_mul]` and
   `simp [Finset.sum_neg_distrib]`, the flipped sum equals
   `-(∑_x f(x) χ_S(x))`.
5. Chaining, `hcv.trans hflip` says the sum equals its own negation, so
   `linarith` concludes it is `0`.

**Remark.** Evenness of `|S|` enters at exactly one point, `hone`. Run the same
involution with `|S|` odd and the two sign flips cancel, giving the vacuous
`Σ = Σ` — which is why the odd levels carry all of an odd function's weight.

**Used in.** `ArrowTheorem.lean`, as the tool that restricts Arrow's Fourier
bookkeeping to odd levels: `corrFunc_ge_neg_third` (line 203), the
`corrFunc = -1/3` characterisation (line 241), and its inner even-frequency case
(line 272).
