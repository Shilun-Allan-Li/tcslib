<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/Basic.lean :: add -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Pointwise addition of codewords

**Definition.** For codewords `c₁ c₂ : Codeword n α`, `add c₁ c₂` is the
codeword `fun i ↦ c₁ i + c₂ i` — coordinatewise sum in the alphabet `α`. Since
`Codeword n α` is an `abbrev` for `Fin n → α`, this is just the function whose
`i`-th coordinate is the sum of the `i`-th coordinates. The ambient `variable`
block gives `α` a `Field` instance, which is where the `+` comes from.

It is not registered as an `Add (Codeword n α)` instance, so `c₁ + c₂` does not
elaborate to this; it must be written `Codeword.add c₁ c₂`. (The pointwise `Pi`
instance would in any case give the same function.) It carries `@[simp]`, so the
definition unfolds on sight and any goal mentioning it is immediately rewritten
to the coordinatewise form.

**Note for reviewers.** No Lean file in the repository refers to `add`; the only
reference outside `Basic.lean` is the `\lean{...}` entry in
`blueprint/src/chapter/ErrorCorrectingCodes/Basic.tex`. It is dead as of this
pass, present for symmetry with `sub` and `zero` in the codeword-algebra group.
