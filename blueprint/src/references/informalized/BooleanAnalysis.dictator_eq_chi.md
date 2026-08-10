<!-- generated-by: proofmatch informalization (not_in_text) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Basic.lean :: dictator_eq_chi -->
<!-- origin: boolean-ch02-social-choice-arrow run 352ab7ff3113 verdict not_in_text (0.82) -->

# The dictator is a singleton character

**Claim.** For each coordinate `i : Fin n`, the dictator function
`dictator i = fun x ↦ boolToSign (x i)` is equal, as a function, to the
Walsh–Fourier character at the singleton frequency: `dictator i = chiS {i}`.

**Proof.**

1. `ext x` reduces the equality of functions to a pointwise equality at an
   arbitrary `x : BoolCube n`.
2. `simp [dictator, chiS]` unfolds both sides: the left is `boolToSign (x i)`,
   and the right is `∏ j ∈ {i}, boolToSign (x j)`, which collapses by the
   singleton-product simp set (the same step packaged as `chiS_singleton`).

**Remark.** Purely definitional — it is the bridge that lets a dictator be
handled by the Fourier machinery. Used in `BooleanAnalysis/ArrowTheorem.lean`,
where a function with all Fourier weight on `{i}` is identified as the `i`-th
dictator.
