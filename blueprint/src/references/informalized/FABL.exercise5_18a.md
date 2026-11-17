<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/MajorityLimits.lean :: FABL.exercise5_18a -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binomial series for the inverse square root

**Claim.** If $|z|<1$, then $\sum_{j\ge0}\binom{2j}{j}z^{2j}/2^{2j}=(1-z^2)^{-1/2}$.

**Proof.** The hypothesis $|z|<1$ gives $z^2<1$. Apply the generalized binomial power series for $1/(1-w)^{1/2}$ at $w=z^2$, which is inside its convergence ball. Its $j$th coefficient is the generalized binomial coefficient $\operatorname{multichoose}(1/2,j)$. The identity relating that coefficient to the central binomial coefficient (`FABL.multichoose_one_half_eq_centralBinom`) rewrites the terms as $\binom{2j}{j}z^{2j}/2^{2j}$. The sum is therefore $1/(1-z^2)^{1/2}$. Since $1-z^2\ge0$, the real-power identity for exponent $-1/2$ identifies this with $(1-z^2)^{-1/2}$.

**Key facts.** `FABL.multichoose_one_half_eq_centralBinom`.
