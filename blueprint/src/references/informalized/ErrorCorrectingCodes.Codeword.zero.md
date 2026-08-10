<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/Basic.lean :: zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The all-zeros codeword

**Definition.** `zero : Codeword n α` is the constant function
`fun (_ : Fin n) ↦ 0`, i.e. the length-`n` word every coordinate of which is the
additive identity of `α` (supplied by the ambient `Field α` instance). Both `n`
and `α` are implicit, so the block length is inferred from the use site. It is
marked `@[simp]`, so it unfolds to the constant lambda on sight.

Like `add` and `sub`, it is a bare definition rather than a `Zero
(Codeword n α)` instance; `(0 : Codeword n α)` therefore elaborates via the `Pi`
instance and is a *different term*, propositionally equal but not syntactically
so. Occurrences in the codebase consistently write `zero` or `Codeword.zero`.

**Used in.** `weight c := hamming_distance c zero` in this file — the Hamming
weight is defined as the distance to this word, which is what makes it the
reference point of the whole weight development. Also used directly in
`HammingBound.lean` (the `h_card_x0` sphere-size step) and in
`GilbertVarshamov.lean`, where `hamming_ball (d-1) zero` is the low-weight ball.
