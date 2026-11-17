<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Randomization/General.lean :: BooleanAnalysis.Hypercontractivity.randomization_pointwise_parseval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pointwise randomization Parseval identity

**Claim.** For each fixed outcome, the uniform average over Boolean signs of the squared randomized expansion equals the sum of the squares of its orthogonal components.

**Proof.** Fix the outcome and regard its randomized expansion as a function on the Boolean cube. Parseval’s identity for the Boolean Fourier basis states that the uniform average of the square of this function is the sum of the squares of all its Fourier coefficients (`BooleanAnalysis.parseval`). The Fourier coefficient at a set $S$ is exactly the component indexed by $S$ at the fixed outcome (`randomization_fourier_coefficient`). Substituting these coefficients into Parseval gives the claimed identity.

**Key facts.** `BooleanAnalysis.Hypercontractivity.randomization_fourier_coefficient`, `BooleanAnalysis.parseval`.
