<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/NoiseStability/NoiseKernels.lean :: FABL.pmfExpectation_add -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Additivity of Expectation

**Claim.** For functions $f,g$ on a finite set, expectation of their sum is the sum of their expectations.

**Proof.** Expand expectation as the finite sum of probability weights times function values. Distribute each weight over $f(x)+g(x)$, then distribute the finite sum over addition. The resulting two sums are precisely the expectations of $f$ and $g$.
