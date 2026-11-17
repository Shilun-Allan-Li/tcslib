<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/Peres.lean :: FABL.sqrt_inverseNoiseFloor_le_sqrt_three_halves_mul_sqrt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Inverse Noise Floor Bound

**Claim.** For $0<\delta\le \tfrac12$, if $N=\lfloor 1/\delta\rfloor$, then $\sqrt{1/N}\le \sqrt{3/2}\,\sqrt{\delta}$.

**Proof.** Put $t=1/\delta$ and $m=N$. Since $\delta\le \tfrac12$, we have $t\ge2$. We first show $\tfrac23t\le m$. If $t<3$, then $m=\lfloor t\rfloor\ge2$, while $\tfrac23t<2$. If $t\ge3$, the floor estimate $t-1<m$ applies, and $\tfrac23t\le t-1$ follows from $t\ge3$. Thus in either case $\tfrac23t\le m$. Multiplying by $\delta>0$ and using $t\delta=1$ gives $\tfrac23\le m\delta$, hence $1/m\le\tfrac32\delta$ because $m>0$. The square root is increasing on nonnegative reals, so $\sqrt{1/m}\le\sqrt{(3/2)\delta}=\sqrt{3/2}\,\sqrt\delta$.
