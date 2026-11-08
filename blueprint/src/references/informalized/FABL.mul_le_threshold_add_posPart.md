<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/GaussianSharpLevelOne.lean :: FABL.mul_le_threshold_add_posPart -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Threshold and positive-part bound

**Claim.** For real numbers $r,y,t$ with $0\le r\le1$, we have $ry\le tr+\max(y-t,0)$.

**Proof.** Split according to whether $y\le t$. In that case the positive part $(y-t)^+$ is zero. Since $r\ge0$ and $t-y\ge0$, we have $r(t-y)\ge0$, which rearranges to $ry\le tr$. If instead $y>t$, then $(y-t)^+=y-t$. Now $1-r\ge0$ and $y-t>0$, so $(1-r)(y-t)\ge0$. Expanding and rearranging gives $ry\le tr+(y-t)$.
