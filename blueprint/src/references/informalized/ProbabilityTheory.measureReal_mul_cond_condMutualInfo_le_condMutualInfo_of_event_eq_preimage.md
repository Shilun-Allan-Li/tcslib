<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/Entropy/ChainRules.lean :: ProbabilityTheory.measureReal_mul_cond_condMutualInfo_le_condMutualInfo_of_event_eq_preimage -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Conditional mutual information on an event

**Claim.** If $A$ is the event that $Z$ lies in a measurable set $B$, then $\mu(A)$ times the conditional mutual information of $X$ and $Y$ given $Z$ under the measure conditioned on $A$ is at most their conditional mutual information under $\mu$.

**Proof.** Expand each conditional mutual information as a sum over the values $z$ in the finite range of $Z$, and distribute the factor $\mu(A)$ across the sum. Fix such a value $z$, and let $F=Z^{-1}\{z\}$. If $z\in B$, then $F\subseteq A$. Conditioning first on $A$ and then on $F$ is therefore the same as conditioning directly on $F$ (`ProbabilityTheory.cond_cond_eq_cond_of_subset`). Also, the mass of $F$ under the conditional measure, multiplied by $\mu(A)$, is its original mass (`ProbabilityTheory.measureReal_mul_cond_real_eq_measureReal_of_subset`). Consequently, the summand on the conditioned side equals the corresponding summand under the original measure. If $z\notin B$, then $A\cap F=\varnothing$, so $F$ has conditional mass zero under conditioning on $A$ and the left summand vanishes. The corresponding right summand is nonnegative, since it is the mass of $F$ times a nonnegative mutual information. Thus each summand on the left is at most its counterpart on the right; summing gives the result.

**Key facts.** `ProbabilityTheory.cond_cond_eq_cond_of_subset`, `ProbabilityTheory.measureReal_mul_cond_real_eq_measureReal_of_subset`.
