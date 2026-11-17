<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/KKLBribery.lean :: FABL.indicator_pair_le_of_imp -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of paired indicators

**Claim.** If $P_+$ implies $A_+$ and $P_-$ implies $A_-$, then the sum of the two indicators for $P_+,P_-$ is at most the sum of the indicators for $A_+,A_-$.

**Proof.** Each implication ensures that whenever one of $P_+$ or $P_-$ holds, its corresponding proposition $A_+$ or $A_-$ also holds. Thus each indicator on the left is at most its corresponding indicator on the right. Adding these two inequalities gives the result.
