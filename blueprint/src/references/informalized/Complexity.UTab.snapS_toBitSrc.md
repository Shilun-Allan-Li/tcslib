<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableauSpec.lean :: Complexity.UTab.snapS_toBitSrc -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Snapshot Source Translation

**Claim.** Under the stated register-value assumptions, translating each entry of the snapshot-source list at the snapshot width and with the initial-time flag set according to $t=0$ gives exactly the tableau bit-source list at time $t$.

**Proof.** Expand the snapshot-source list into its initial entries, its work-tape boundary entries, and the repeated previous-snapshot sources. The repeated portion translates to the previous-snapshot source list by the previously established translation formula (`Complexity.UTab.psnS_toBitSrc`). For the first entries, use $\rho(r_I)=\operatorname{snapIdx}_M(N,T,t)$ and $|\ell|=N$. If $t=0$, the initial-time flag makes the previous-snapshot entry the false constant, as in the tableau definition. If $t>0$, write $t=t'+1$; substituting the register values and expanding the stride shows that the translated block index is the snapshot index at time $t-1$, and the remaining input-block indices agree with those in the tableau layout. For each work tape $\tau$, the translated boundary entry has block index $\rho(r_{LB})+(\tau+1)(2\rho(r_T)+1)-1$. Substituting $\rho(r_{LB})=t\,\operatorname{cfgStride}_M(N,T)$ and $\rho(r_T)=T$ reduces this to the cell index at time $t$ and offset $2T$. Thus every component agrees in order, proving equality of the lists.

**Key facts.** `Complexity.UTab.psnS_toBitSrc`.
