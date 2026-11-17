<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/FoolingF₂Polynomials/ViolaSeedLength.lean :: FABL.logb_smallBiasSupportEnvelope_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Logarithmic Bias Support Identity

**Claim.** For natural numbers $n,d$, with $n>0$ and $\varepsilon>0$, set $b=(\varepsilon/9)^{2^{d-1}}$, where $d-1$ is truncated natural subtraction. Then $\log_2(16(n/b)^2)=4+2(\log_2 n+2^{d-1}\log_2(9/\varepsilon))$.

**Proof.** Both $n$ and $b$ are positive, so the logarithm rules for products, powers, and quotients apply. Expanding gives $\log_2 16+2(\log_2 n-\log_2 b)$. Since $16=2^4$, the first term is $4$. The definition of $b$ and the logarithm rule for a positive real power give $\log_2 b=2^{d-1}\log_2(\varepsilon/9)=-2^{d-1}\log_2(9/\varepsilon)$. Substitution and rearrangement give the stated identity.

**Key facts.** `FABL.violaBaseBias_pos`.
