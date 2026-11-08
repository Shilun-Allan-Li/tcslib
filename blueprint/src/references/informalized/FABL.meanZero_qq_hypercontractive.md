<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/OneBitHypercontractivity.lean :: FABL.meanZero_qq_hypercontractive -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Mean-zero equal-exponent hypercontractivity

**Claim.** If a real-valued random variable on a finite nonempty space has mean zero, then for $q\ge1$ it is $(q,q,\rho)$-hypercontractive for every $0\le\rho\le1$.

**Proof.** To verify hypercontractivity, fix real numbers $a,b$. The coercion lemma identifies each extended-real-indexed norm at exponent $q$ with the corresponding real-exponent norm. The mean-zero equal-exponent contraction inequality then says that the norm of $a+\rho bX$ is at most the norm of $a+bX$, using $q\ge1$ and $0\le\rho\le1$. This is the required inequality for every $a,b$, hence the stated hypercontractivity.

**Key facts.** `FABL.uniformLpNormENNReal_coe`, `FABL.meanZero_qq_hypercontractive_real`.

**Caveat.** The supplied informal statement mentions additional parts (b) and (c), but the formal declaration and proof provided establish only the equal-exponent assertion for $0\le\rho\le1$.
