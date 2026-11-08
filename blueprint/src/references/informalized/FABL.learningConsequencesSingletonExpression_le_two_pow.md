<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/LearningConsequencesResources.lean :: FABL.learningConsequencesSingletonExpression_le_two_pow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exponential bound for a singleton expression

**Claim.** For all nonnegative integers $n,C,Q$, with the stated coefficients, the singleton expression is at most the indicated power of $2$.

**Proof.** Set $s=\sqrt{\lceil\log_2(n+1)\rceil}+1$, $A=8(C+1)(Q+1)+1$, $R_0=(8(C+1)(Q+1))^4$, and let $H$ be the stated exponent coefficient. Since $s\geq1$, the elementary bound $m\leq 2^m$ gives $R_0\leq 2^{R_0s}$. Applying the same bound to $s$ and raising to the fourth power gives $s^4\leq2^{4s}$. Also, $9\leq16=2^4$, so raising to the power $2As$ yields $9^{2As}\leq2^{8As}$. Multiplying these three estimates bounds the whole left-hand side by $2^{R_0s}2^{4s}2^{8As}=2^{(R_0+8A+4)s}$. By the definition of $H$, this is exactly $2^{Hs}$, as required.

**Key facts.** `FABL.nat_self_le_two_pow`.
