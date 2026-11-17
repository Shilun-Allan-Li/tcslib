<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/KKLBribery.lean :: FABL.log_one_add_two_mul_briberyRate_ge -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Logarithmic Bribery Rate Bound

**Claim.** For every integer $n\ge2$, if $r=\log(n)/(100n)$, then $r\le\log(1+2r)$.

**Proof.** The established bounds on the bribery rate give $0<r\le1/2$, so $1+2r>0$. Apply $\log y\le y-1$ to $y=(1+2r)^{-1}$ and use $\log(y^{-1})=-\log y$. This yields $\log(1+2r)\ge 1-(1+2r)^{-1}=2r/(1+2r)$. Since $r>0$ and $r\le1/2$, we have $r(1+2r)\le2r$, hence $r\le2r/(1+2r)$. Combining the inequalities proves the claim.

**Key facts.** `FABL.briberyRate_pos`, `FABL.briberyRate_le_one_half`.
