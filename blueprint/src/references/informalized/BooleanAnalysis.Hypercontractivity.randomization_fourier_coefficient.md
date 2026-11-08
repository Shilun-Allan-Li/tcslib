<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Randomization/ProjectionBounds.lean :: BooleanAnalysis.Hypercontractivity.randomization_fourier_coefficient -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier coefficients of randomization

**Claim.** For fixed outcome \(x\), the Walsh–Fourier coefficient at \(S\) of the function of the random seed given by the randomization is the \(S\)-component of \(f\) at \(x\).

**Proof.** For fixed \(x\), the randomization is a linear combination of Walsh characters, with coefficient at each subset \(T\) equal to the component indexed by \(T\) evaluated at \(x\). The Fourier coefficient of such a character expansion at \(S\) extracts precisely its \(S\)-coefficient, by the character orthogonality formula (\(\texttt{DecisionTree.fourierCoeff\_sum\_chiS}\)).

**Key facts.** `DecisionTree.fourierCoeff_sum_chiS`.
