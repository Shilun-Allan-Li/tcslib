<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LearningTheory/FiniteFamily.lean :: FABL.finiteFamilyCoefficientFailureBits_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Failure Bits for a Finite Family

**Claim.** For a nonempty finite family $\mathcal{F}$, the failure-bit count at confidence parameter $1/(10|\mathcal{F}|)$ is $\operatorname{clog}_2(20|\mathcal{F}|)$.

**Proof.** Substituting the confidence parameter into the definition of the failure-bit count gives $\operatorname{clog}_2\!\left(\left\lceil 2/(1/(10|\mathcal{F}|))\right\rceil\right)$. Since the family is nonempty, its cardinality is positive, and the rational quantity inside the ceiling simplifies exactly to the natural number $20|\mathcal{F}|$. The ceiling of a natural number is that number, yielding the claimed expression.
