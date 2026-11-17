<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/RademacherFirstMoment.lean :: FABL.thirdMomentSum_rademacherSummand -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Third Moments of Rademacher Summands

**Claim.** For independent uniform signs, the sum of the third absolute moments of the summands $a_iX_i$ is $\sum_i |a_i|^3$.

**Proof.** By definition, the third-moment sum is the sum over coordinates of the expectations of $|a_iX_i|^3$. For each coordinate, the sign value is either $-1$ or $1$, so $|a_iX_i|^3=|a_i|^3$ for every outcome. The expectation of this constant is itself: integration under the uniform-sign measure is the same as uniform expectation ( `integral_uniformPMF_eq_expect`), and the expectation of a constant equals that constant. Thus each summand contributes $|a_i|^3$, giving the stated sum.

**Key facts.** `FABL.integral_uniformPMF_eq_expect`, `FABL.signValue_eq_neg_one_or_one`.
