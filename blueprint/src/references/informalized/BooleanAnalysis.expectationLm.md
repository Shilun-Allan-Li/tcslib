<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Basic.lean :: expectationLm -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The coordinate averaging operator as a linear map

**Definition.** `expectationLm i : BooleanFunc n →ₗ[ℝ] BooleanFunc n` bundles the
`i`-th expectation (averaging) operator into an `ℝ`-linear map:

- `toFun := expectationOperator i`, where
  `expectationOperator i f x = (f (Function.update x i false) + f (Function.update x i true)) / 2`
  — the *average* of `f` over the two values of coordinate `i`, the other
  coordinates held at `x`;
- `map_add' := expectation_add i` and `map_smul' := expectation_smul i`, each by
  `ext x`, `simp only [expectationOperator, Pi.add_apply / Pi.smul_apply,
  smul_eq_mul]`, `ring`.

**Remark.** It is the companion of `derivativeLm` under the standard
one-coordinate decomposition `f = E_i f + x_i · D_i f`: averaging keeps exactly
the frequencies missing `i` (killing every `f̂(S)` with `i ∈ S`), while the
derivative keeps exactly those containing it. Sum and difference of the same two
evaluations, hence the near-identical proofs.

**No `sorry`** anywhere in the block. Three caveats, all non-mathematical — the
statements are correct, only the surrounding prose and the reachability are off:

- The docstring above `expectationOperator` is copy-pasted from `derivative`: it
  claims `f'(x) = (f(x⁺ⁱ) - f(x⁻ⁱ))/2` with a **minus**, while the body sums the
  two evaluations. It also repeats the derivative's `x⁺ⁱ`/`x⁻ⁱ` gloss verbatim.
- The docstring above `expectation_smul` likewise reads "The discrete
  derivative operator commutes with scalar multiplication."
- Like `derivativeLm`, it is **unused**: neither `expectationLm` nor
  `expectationOperator` is referenced anywhere in `TCSlib/` outside this block
  (`expectationOperator` only by its own two linearity lemmas and this
  bundling).

**Used in.** Nothing yet — see above.
