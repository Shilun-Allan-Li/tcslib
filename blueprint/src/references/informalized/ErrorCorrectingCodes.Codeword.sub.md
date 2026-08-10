<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/Basic.lean :: sub -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Pointwise subtraction of codewords

**Definition.** For codewords `c₁ c₂ : Codeword n α`, `sub c₁ c₂` is the
codeword `fun i ↦ c₁ i - c₂ i` — coordinatewise difference in the alphabet `α`,
whose subtraction comes from the ambient `Field α` instance. As with `add`, this
is a plain function definition on `Fin n → α`, not a `Sub (Codeword n α)`
instance, so it must be applied by name rather than through `-`. It is marked
`@[simp]` and therefore unfolds automatically.

For a linear code, `sub c₁ c₂` is the difference vector whose Hamming weight
equals `hamming_distance c₁ c₂`; that identity is the usual route from minimum
distance to minimum nonzero weight, but it is not proved anywhere in this file.

**Note for reviewers.** No Lean file in the repository refers to `sub`; the only
reference outside `Basic.lean` is the `\lean{...}` entry in
`blueprint/src/chapter/ErrorCorrectingCodes/Basic.tex`. It is dead as of this
pass. `weight` is defined via `hamming_distance c zero` rather than through
`sub`, so the codeword-difference route is unused.
