<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Cube/Bonami.lean :: uniformMeasure -->
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

**Used in.** `BooleanAnalysis.Hypercontractivity.lowDegree_anticoncentration` in `TCSlib/BooleanAnalysis/Hypercontractivity/Applications/LowDegree.lean`; `BooleanAnalysis.Hypercontractivity.bonami_lemma`, `BooleanAnalysis.Hypercontractivity.instIsProbabilityMeasureBoolCubeUniformMeasure`, `BooleanAnalysis.Hypercontractivity.uniformMeasure_apply` in `TCSlib/BooleanAnalysis/Hypercontractivity/Cube/Bonami.lean`.
