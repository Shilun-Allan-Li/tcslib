<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/LearningConsequences.lean :: FABL.boundedFamilyCoefficientAccuracy_le_finiteFamilyCoefficientAccuracy -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded Family Accuracy Comparison

**Claim.** If the finite family is nonempty, its cardinality is at most the positive integer $M$, and $\varepsilon>0$, then $\varepsilon/(2M)\le\varepsilon/(2|\mathcal F|)$.

**Proof.** Nonemptiness gives $|\mathcal F|>0$, and the assumption gives $0<M$ as well. Since $|\mathcal F|\le M$, we have $2|\mathcal F|\le 2M$. For positive denominators, increasing the denominator weakly decreases a quotient with fixed nonnegative numerator. Taking the numerator to be $\varepsilon$ yields the result.
