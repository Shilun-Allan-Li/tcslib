<!-- generated-by: proofmatch informalization (not_in_text) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Basic.lean :: chiS_singleton -->
<!-- origin: boolean-ch02-social-choice-arrow run 352ab7ff3113 verdict not_in_text (0.62) -->

# The character of a singleton is a single sign

**Claim.** For a coordinate `i : Fin n` and a point `x : BoolCube n`, the
Walsh–Fourier character at the singleton frequency `{i}` is just the sign of the
`i`-th bit: `χ_[{i}] x = boolToSign (x i)`.

**Proof.**

1. Unfold `chiS`: by definition `χ_[S] x = ∏ j ∈ S, boolToSign (x j)`, so the
   goal becomes `∏ j ∈ {i}, boolToSign (x j) = boolToSign (x i)`.
2. `simp [chiS]` closes it — the product over a singleton collapses via
   `Finset.prod_singleton`.

**Remark.** This is a definitional unfolding, not a mathematical step; it is
registered `@[simp]` so that singleton characters disappear automatically. It is
used where dictators are rewritten as characters, e.g. `dictator_eq_chi`'s
consumers in `BooleanAnalysis/ArrowTheorem.lean` and
`BooleanAnalysis/LMN/DecisionTreeFourier.lean`.
