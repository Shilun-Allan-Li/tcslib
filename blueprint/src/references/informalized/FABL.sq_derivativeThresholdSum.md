<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/PolynomialThresholdInfluence.lean :: FABL.sq_derivativeThresholdSum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Square of the Derivative Threshold Sum

**Claim.** For the threshold signs defined from the coordinate derivatives of $p$, the square of their signed sum is $n$ plus the sum of all off-diagonal pair products.

**Proof.** Write $a_i=x_iq_i(x)$ for each coordinate, where $q_i(x)$ is the threshold sign of the derivative. Expanding the square of $\sum_i a_i$ as a double sum gives $\sum_i\sum_j a_i a_j$. For each fixed $i$, separate the diagonal term $a_i^2$ from the terms with $j\ne i$. Each diagonal term is $1$, since both $x_i$ and the threshold output are signs; the fact that their product squares to one is `derivativeThresholdSummand_sq`. Summing these diagonal terms gives $n$. The remaining terms are precisely the stated off-diagonal sum after substituting $a_i=x_iq_i(x)$ and rearranging the real factors.

**Key facts.** `FABL.derivativeThresholdSummand_sq`.
