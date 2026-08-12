<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Basic.lean :: BooleanFunc -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Real-valued functions on the hypercube

**Definition.** `BooleanFunc n := BoolCube n → ℝ` — the functions the Fourier
theory is developed for.

- The codomain is `ℝ`, **not** `{-1,1}`. Being `±1`-valued is the separate
  predicate `isPmOne f : ∀ x, f x = 1 ∨ f x = -1`, assumed only where it is
  actually needed (`innerProduct_self_pm_one`, `parseval_pm_one`,
  `arrow_theorem`). Fourier coefficients, characters and noise-operator images
  are all genuinely real-valued, so the wider type is the right one.
- As an `abbrev` for a Pi type into `ℝ`, it silently inherits the `Pi`
  algebraic structure (`Pi.add_apply`, `Pi.smul_apply`, `Pi.module`). That
  inheritance is what makes `f + g` and `c • f` typecheck in
  `derivative_add` / `derivative_smul`, and what lets `derivativeLm` and
  `expectationLm` be stated as `BooleanFunc n →ₗ[ℝ] BooleanFunc n`.

**Remark.** Because the abbrev is reducible, a `BooleanFunc n` and a bare
`(Fin n → Bool) → ℝ` are interchangeable to the elaborator — lemmas stated for
one apply to the other without a coercion.

**Used in.** The carrier type throughout: `expect`, `innerProduct`, `l2Norm`,
`chiS`, `fourierCoeff`, `influence`, `noiseOp`, `derivative`,
`expectationOperator`, and every statement in `ArrowTheorem.lean` and
`KKL.lean`.
