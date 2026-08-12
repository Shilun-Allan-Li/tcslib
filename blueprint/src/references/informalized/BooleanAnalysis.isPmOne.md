<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Basic.lean :: isPmOne -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Being a ±1-valued function

**Definition.** For `f : BooleanFunc n`,

```
isPmOne f ↔ ∀ x : BoolCube n, f x = 1 ∨ f x = -1
```

the predicate "`f` is `{-1, 1}`-valued". A plain `def` into `Prop` with no proof
content.

**Remark.** This is the bridge between the real-valued setting the file actually
works in (`BooleanFunc n = BoolCube n → ℝ`, chosen so that Fourier expansion is
linear algebra) and genuine Boolean functions. Its whole force is squeezed out
by `innerProduct_self_pm_one`: `f x * f x = 1` pointwise, hence `⟪f, f⟫ = 1`,
hence `parseval_pm_one`, i.e. `∑_S f̂(S)² = 1`. Nearly every downstream use is
really a use of that normalisation.

**Used in.** Widely, almost always as a hypothesis rather than a goal.
In `Basic.lean`: `innerProduct_self_pm_one` and `parseval_pm_one`.
In `KKL.lean`: `expect_sq_pm_one`, `noisyInfluence_power_bound`, `KKL_balanced`,
`friedgut_junta`, `balanced_totalInfluence_ge_one`.
In `ArrowTheorem.lean`: `corrFunc_ge_neg_third`, `acyclic_implies_corrFunc`,
`arrow_theorem` and two further lemmas.
Discharged as a goal exactly once, in `LMN/FourierConcentration.lean` (line 48),
where `fun x => boolToSign (g x)` is shown to be `±1`-valued — the point at
which an honest `Bool`-valued function enters the real-valued theory.
