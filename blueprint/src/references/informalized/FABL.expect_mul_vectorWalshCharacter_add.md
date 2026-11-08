<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/InnerProductModTwo.lean :: FABL.expect_mul_vectorWalshCharacter_add -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Averaged Walsh Character Identity

**Claim.** For $a,b\in(\mathbb F_2)^n$, the uniform expectation over $x$ and $y$ of $\chi_a(x)\chi_{x+b}(y)$ equals the uniform expectation over $x$ of $\chi_a(x)$ times the indicator of $x=b$.

**Proof.** Fix $x$ and average first over $y$. The expectation of a Walsh character is $1$ when its index is zero and $0$ otherwise (\texttt{FABL.expect\_vectorWalshCharacter}). Thus the inner average of $\chi_{x+b}(y)$ is the indicator that $x+b=0$. In the vector space over $\mathbb F_2$, this condition is equivalent to $x=b$ (\texttt{FABL.add\_eq\_zero\_iff\_eq\_f₂Cube}). The factor $\chi_a(x)$ is constant in $y$, so it remains outside the inner average, giving the identity after averaging over $x$.

**Key facts.** `FABL.expect_vectorWalshCharacter`, `FABL.add_eq_zero_iff_eq_f₂Cube`.
