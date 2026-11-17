<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/Entropy/ChainRules.lean :: ProbabilityTheory.measureReal_mul_cond_real_eq_measureReal_of_subset -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Mass formula for nested conditioning

**Claim.** For a finite measure, a measurable set $A$, and a measurable-set subset $F\subseteq A$, the mass of $F$ under the measure conditioned on $A$, multiplied by the mass of $A$, equals the original mass of $F$.

**Proof.** The conditional-measure formula expresses the conditional mass of $F$ as $\mu(A\cap F)/\mu(A)$ when $\mu(A)>0$. Since $F\subseteq A$, the intersection is $F$, and multiplying by $\mu(A)$ gives the claim. The proof also handles zero mass: monotonicity gives $0\leq\mu(F)\leq\mu(A)=0$, so both sides are zero.
