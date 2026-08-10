<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Bonami.lean :: uniformMeasure -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The uniform measure on the Boolean hypercube

**Definition.** `uniformMeasure n` is the measure on `BoolCube n = Fin n → Bool`
obtained by pushing the Mathlib PMF `PMF.uniformOfFintype (BoolCube n)` through
`PMF.toMeasure`. It is the canonical uniform probability measure on the
`2^n`-point cube, declared `noncomputable`.

This is a plain definition — no proof content. Two facts are registered next to
it in the same file:

- an `instance : IsProbabilityMeasure (uniformMeasure n)`, discharged by
  `unfold uniformMeasure; infer_instance` from the corresponding
  `PMF.toMeasure` instance;
- `uniformMeasure_apply`, which identifies the measure of a singleton with the
  combinatorial weight: `((uniformMeasure n) {x}).toReal = uniformWeight n`,
  where `uniformWeight n = (2 : ℝ)⁻¹ ^ n`.

**Used in.** The `IsBReasonable`/moment machinery of the Bonami lemma:
`moment_eq_expect` converts `moment f p P` into `expect (fun x ↦ f x ^ p)` for
any probability measure whose singletons have mass `uniformWeight n`, and
`uniformMeasure` together with `uniformMeasure_apply` is the instance that
hypothesis is applied to. It exists to bridge the measure-theoretic statement
of hypercontractivity and the finite-average (`expect`) formulation used
elsewhere in `BooleanAnalysis`.
