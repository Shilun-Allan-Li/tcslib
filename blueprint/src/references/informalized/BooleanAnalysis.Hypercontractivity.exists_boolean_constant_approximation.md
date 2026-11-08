<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Applications/KKL/Rounding.lean :: BooleanAnalysis.Hypercontractivity.exists_boolean_constant_approximation -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Boolean Constant Approximation

**Claim.** Every Boolean-valued function on the Boolean cube has a Boolean constant function whose disagreement probability with it is at most half its cube variance.

**Proof.** Apply the Boolean junta approximation result obtained from Fourier omission with the coordinate set chosen to be empty (`exists_boolean_junta_of_fourier_omission`). It gives a Boolean function $h$ depending only on the empty set, hence a constant, and bounds its disagreement probability by half the sum of the nonempty Fourier coefficient squares. The variance identity expressing cube variance as exactly that sum (`cubeVariance_eq_sum_nonempty_fourier`) turns this bound into disagreement probability at most half the cube variance, as required.

**Key facts.** `BooleanAnalysis.Hypercontractivity.exists_boolean_junta_of_fourier_omission`, `BooleanAnalysis.Hypercontractivity.cubeVariance_eq_sum_nonempty_fourier`.
