<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/GeneralizedFourierFormulas.lean :: FABL.productDegree_le_of_isSumOfJuntasAtMost -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Degree bound from a junta decomposition

**Claim.** If $f$ is a sum of juntas at most $k$, then its product degree is at most $k$.

**Proof.** The product degree is defined as the least natural number $m$ for which $f$ is a sum of juntas at most $m$. The dimension bound supplies such a decomposition with bound $n$ (`isSumOfJuntasAtMost_dimension`), so the least witness exists. Since the hypothesis supplies a witness with bound $k$, the least witness is no larger than $k`, by the defining minimality property of the natural-number least witness.

**Key facts.** `FABL.isSumOfJuntasAtMost_dimension`.
