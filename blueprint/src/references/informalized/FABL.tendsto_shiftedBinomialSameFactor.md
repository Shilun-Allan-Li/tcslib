<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/GotsmanLinialExtremizer.lean :: FABL.tendsto_shiftedBinomialSameFactor -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Shifted Binomial Factor Limit

**Claim.** For fixed natural numbers $c$ and $j$ with $j\le c$, the quantity $(2m+c+1)/(2(m+c+1-j))$ tends to $1$ as $m\to\infty$.

**Proof.** Rewrite the denominator using $m+c+1-j=m+(c+1-j)$. The expression is then a quotient of affine functions of $m$, with leading coefficient $2$ in both numerator and denominator. The standard limit for such quotients is the ratio of their leading coefficients, hence $1$.
