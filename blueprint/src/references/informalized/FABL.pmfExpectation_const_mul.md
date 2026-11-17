<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/NoiseStability/NoiseKernels.lean :: FABL.pmfExpectation_const_mul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Scaling an expectation

**Claim.** For a finite probability mass function, the expectation of $x\mapsto c f(x)$ is $c$ times the expectation of $f$.

**Proof.** Expand the expectation as a finite sum of probability weights times function values. Distribute the scalar $c$ across that sum, then use associativity and commutativity of real multiplication to identify each summand with $c$ times the corresponding summand in the expectation of $f$. Factoring out $c$ gives the result.
