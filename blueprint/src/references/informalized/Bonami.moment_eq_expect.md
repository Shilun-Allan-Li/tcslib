<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Bonami.lean :: moment_eq_expect -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Moments under a singleton-uniform measure are hypercube expectations

**Claim.** Let `f : BooleanFunc n` be a real-valued function on the cube
`BoolCube n = Fin n → Bool`, let `p : ℕ`, and let `P` be a probability measure on
`BoolCube n` all of whose singletons carry mass `uniformWeight n = 2⁻ⁿ`
(`hP_unif : ∀ x, (P {x}).toReal = uniformWeight n`). Then Mathlib's
measure-theoretic `p`-th moment agrees with the combinatorial average:
`moment f p P = expect (fun x ↦ f x ^ p) = 2⁻ⁿ · ∑_x f x ^ p`. This is purely a
bridge lemma — its only content is trading the Bochner integral for the finite
sum that the rest of `BooleanAnalysis` uses.

**Proof.**

1. `rw [moment]` turns the left side into the integral `∫ x, (f ^ p) x ∂P`.
2. `simp only [Pi.pow_apply, Integrable.of_finite, integral_fintype, smul_eq_mul]`:
   `BoolCube n` is a `Fintype`, so `MeasureTheory.Integrable.of_finite` gives
   integrability for free and `MeasureTheory.integral_fintype` rewrites the
   integral as `∑ x, P.real {x} * f x ^ p`.
3. `unfold expect` and `rw [Finset.mul_sum]` push the constant `uniformWeight n`
   on the right side inside the sum, giving `∑ x, uniformWeight n * f x ^ p`.
4. `apply Finset.sum_congr rfl` with `intro x _` reduces the goal to a single
   term at a fixed point `x`.
5. `hP_unif x` supplies `h_meas_x : P.real {x} = uniformWeight n` (`Measure.real`
   is by definition the `toReal` of the measure), and `rw [h_meas_x]` closes the
   goal, the two factors now being syntactically identical. ∎

**Used in.** `bonami_lemma`, applied twice (`p = 4` and `p = 2`) with
`uniformMeasure_apply` discharging `hP_unif`, which reduces
`IsBReasonable f (uniformMeasure n) (9 ^ k)` to the algebraic bound
`bonami_expect`.
