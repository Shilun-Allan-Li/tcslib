<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/OneBitHypercontractivity.lean :: FABL.IsHypercontractiveRandomVariable.of_normalized -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reduction to Normalized Tests

**Claim.** For nonzero exponents $p,q$, if the asserted norm inequality holds whenever $a=1$ or $b=1$, then it holds for every pair of real inputs $a,b$.

**Proof.** Fix $a,b$. If $a=0$, use the assumed test with inputs $0,1$. This bounds the $q$-norm of $\rho X$ by the $p$-norm of $X$. Homogeneity of the uniform norms, in the form $\|cf\|=|c|\|f\|$ for a nonzero exponent (`uniformLpNormENNReal_const_mul`), scales this inequality by $|b|$ to give the desired bound for $a=0$. If $a\ne0$, put $t=b/a$ and use the test with inputs $1,t$. Its two functions, after multiplication by $a$, are exactly the target functions. Applying the same homogeneity identity scales the tested inequality by $|a|$ and proves the claim.

**Key facts.** `FABL.uniformLpNormENNReal_const_mul`.
