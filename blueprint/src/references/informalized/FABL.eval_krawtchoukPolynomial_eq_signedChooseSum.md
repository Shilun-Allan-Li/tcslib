<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/KrawtchoukPolynomials.lean :: FABL.eval_krawtchoukPolynomial_eq_signedChooseSum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Krawtchouk Signed Binomial Sum

**Claim.** For natural numbers $n,z,j$ with $z\le n$, the Krawtchouk polynomial satisfies $K_{n,j}(z)=\sum_{k=0}^{j}(-1)^k\binom{z}{k}\binom{n-z}{j-k}$.

**Proof.** Expand the polynomial as its defining finite sum and evaluate each summand at $z$. Evaluation preserves finite sums and products. The first falling-factorial factor, divided by $k!$, evaluates to $\binom{z}{k}$ (`FABL.eval_chooseFactorPolynomial`); the complementary falling-factorial factor, divided by $(j-k)!$, evaluates to $\binom{n-z}{j-k}$ (`FABL.eval_complementChooseFactorPolynomial`). The remaining constant factor is $(-1)^k$. Thus each summand becomes $(-1)^k\binom{z}{k}\binom{n-z}{j-k}$, yielding the stated sum.

**Key facts.** `FABL.eval_chooseFactorPolynomial`, `FABL.eval_complementChooseFactorPolynomial`.
