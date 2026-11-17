<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/ProductLTFNoiseCorrection.lean :: FABL.selectorRetention_mem_Icc -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Selector Retention Probability Bounds

**Claim.** If $\theta\in[-1,1]$, then the retention probability $(1+\theta)/2$ lies in $[0,1]$.

**Proof.** The lower bound $\theta\ge -1$ implies $1+\theta\ge0$, so division by $2$ gives $(1+\theta)/2\ge0$. The upper bound $\theta\le1$ implies $1+\theta\le2$, and hence $(1+\theta)/2\le1$. Together these give the claimed interval membership.
