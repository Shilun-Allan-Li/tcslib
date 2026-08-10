<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/OneBit.lean :: expect_const_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Expectation of a constant is that constant

**Claim.** For `c : ℝ` and any `n`, `expect (fun (_ : BoolCube n) => c) = c` —
the uniform measure on `{0,1}ⁿ` is a probability measure, so averaging a
constant returns it unchanged.

**Proof.** One line. `unfold expect uniformWeight` gives
`(2 : ℝ)⁻¹ ^ n * ∑ x : BoolCube n, c = c`, and
`simp [Finset.sum_const, Finset.card_univ, Fintype.card_bool, Fintype.card_fin]`
evaluates the sum as `2 ^ n * c`, cancelling against `2⁻ⁿ`. ∎

**Used in.** `holder_sharpness`, in the degenerate branch where the normalising
factor `(𝔼[|u|^q])^{1/p}` vanishes and the candidate `f` collapses to a
constant; `private`.
