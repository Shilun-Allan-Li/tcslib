<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/NoiseStability/NoiseKernels.lean :: FABL.pmfExpectation_mul_const -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Scaling a probability expectation

**Claim.** For any real constant $c$, the expectation of $x\mapsto f(x)c$ under $p$ equals $c$ times the expectation of $f$.

**Proof.** Expand the expectation as the finite sum $\sum_x (p(x)).\mathrm{toReal}\,f(x)c$. Since $c$ is independent of the summation index, factor it out of the finite sum. The result is $c\sum_x (p(x)).\mathrm{toReal}\,f(x)$, as claimed.
