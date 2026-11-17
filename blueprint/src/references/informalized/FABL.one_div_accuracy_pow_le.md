<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/LearningConsequencesResources.lean :: FABL.one_div_accuracy_pow_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Power Bound from Accuracy

**Claim.** Under the stated accuracy lower bound, for every natural number $r$, $(1/\varepsilon)^r\le (Q+1)^r$.

**Proof.** Since $\varepsilon>0$, the inequality $1/(Q+1)\le\varepsilon$ can be multiplied by the nonnegative number $Q+1$. Rearranging gives $1/\varepsilon\le Q+1$. Raising both nonnegative sides to the natural power $r$ preserves the inequality, proving the claim.
