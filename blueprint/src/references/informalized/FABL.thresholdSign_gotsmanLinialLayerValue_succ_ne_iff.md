<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/GotsmanLinialExtremizer.lean :: FABL.thresholdSign_gotsmanLinialLayerValue_succ_ne_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Threshold Sign Change in Layer Values

**Claim.** For natural numbers $a,s,c$, the threshold signs of $V(a,s+1,c+1)$ and $V(a,s+1,c)$ differ exactly when $a\le c<a+s+1$.

**Proof.** Set $M=V(a,s,c)$, $u=2c-2a+1$, and $\ell=2c-2a-2s-1$, interpreting these expressions over the reals. Appending the final factor in the product gives $V(a,s+1,c+1)=uM$ and $V(a,s+1,c)=M\ell$ (the layer-value successor identities, `gotsmanLinialLayerValue_succ_count` and `gotsmanLinialLayerValue_succ_degree`). The shorter product is nonzero (`gotsmanLinialLayerValue_ne_zero`), so its sign is either positive or negative. Split into the three cases $c<a$, $c=a$, and $c>a$.

If $c<a$, then $u<0$ and $\ell<0$. Thus $uM$ and $M\ell$ have the same sign, whichever sign $M$ has, so their threshold signs agree. The condition $a\le c<a+s+1$ is false.

If $c=a$, then $u>0$ while $\ell<0$. Multiplication by these factors gives opposite signs for $uM$ and $M\ell$, so their threshold signs differ. Here $a\le c<a+s+1$ holds.

Finally suppose $c>a$. If $c<a+s+1$, then $c\le a+s$, which makes $u>0$ and $\ell<0$. The two products therefore have opposite signs, and the stated interval condition holds. If instead $a+s+1\le c$, then both $u>0$ and $\ell>0$, so the products have the same sign and the interval condition fails. In each case, the threshold-sign conclusions follow from the facts that a negative input has threshold sign $-1$ (`thresholdSign_of_neg`) and a nonnegative input has threshold sign $1$ (`thresholdSign_of_nonneg`).

**Key facts.** `FABL.gotsmanLinialLayerValue_ne_zero`, `FABL.gotsmanLinialLayerValue_succ_count`, `FABL.gotsmanLinialLayerValue_succ_degree`, `FABL.thresholdSign_of_neg`, `FABL.thresholdSign_of_nonneg`.
