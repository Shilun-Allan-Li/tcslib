<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/General.lean :: one_bit_slice_eq_innerProduct -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The one-bit kernel sum of two slices is a one-bit inner product

**Claim.** For `ρ : ℝ`, `f g : BooleanFunc (n + 1)` and fixed `x' y' : BoolCube n`,
the last-coordinate kernel sum
`(1/2) * ∑_{b, b' : Bool} ((1 + ρ · boolToSign b · boolToSign b')/2) · f (snoc x' b) · g (snoc y' b')`
equals `innerProduct (fun t : BoolCube 1 => f (snoc x' (t 0))) (noiseOp ρ (fun t : BoolCube 1 => g (snoc y' (t 0))))`.
So the four-term expression left over after factoring the kernel along the last
bit is literally a one-dimensional noise inner product of the two slices.

**Proof.** A finite computation on `BoolCube 1`, with no mathematical content
beyond enumeration.

1. `unfold noiseOp innerProduct fourierCoeff` and `simp`.
2. `rw [show (Finset.univ : Finset (Finset (Fin 1))) = {∅, {0}} by decide]` —
   there are exactly two Fourier characters in dimension 1; `norm_num; ring_nf`.
3. `unfold expect` / `uniformWeight` and expand the `Fin 1` sums
   (`Finset.sum_range_succ`, `Finset.sum_range_zero`), then
   `rw [show (Finset.univ : Finset (BoolCube 1)) = {fun _ => false, fun _ => true} by decide]`
   and `Finset.sum_pair` to make both sides explicit two-term expressions in
   `boolToSign`.
4. `ring_nf` plus `grind +splitImp` closes the resulting identity; the two
   `Finset.sum_pair` side goals (the two points are distinct) follow from
   `congr_fun h 0` and `simp`.

**Used in.** `two_func_hyp_succ`, in `h_lhs`: it turns the decomposed weighted sum
(`weighted_sum_succ_decomp`) into a kernel average of one-bit inner products, to
which the one-bit `base_case` can be applied pointwise.
