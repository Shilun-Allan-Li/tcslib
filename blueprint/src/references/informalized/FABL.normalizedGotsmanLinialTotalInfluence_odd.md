<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/GotsmanLinialExtremizer.lean :: FABL.normalizedGotsmanLinialTotalInfluence_odd -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Odd-Dimension Influence Identity

**Claim.** For $k>0$, the normalized total influence of the Gotsman–Linial extremizer on the $(k+2m+1)$-dimensional cube equals $\sqrt{k+2m+1}\,M_m\sum_{j=0}^{k-1}Q_{m,k,j}/M_m$.

**Proof.** Set $N=k+2m+1$. Then $N>0$, so $\sqrt N>0$. The starting index in the extremizer’s binomial formula is $\lfloor(N-k)/2\rfloor=m$, and $N-1=2m+k$. Applying the total-influence formula (`totalInfluence_gotsmanLinialExtremizer`) expresses the total influence as $N/2^{N-1}$ times the sum, for $0\le j<k$, of $\binom{2m+k}{m+j}$. By definition, each coefficient divided by $2^{2m+k}$ is $Q_{m,k,j}$. Also $M_m$ is positive (`oddMajorityInfluence_pos`), so the ratios by $M_m$ are legitimate. Dividing the total-influence expression by $\sqrt N$ and rearranging each summand gives $\sqrt N\,M_m(Q_{m,k,j}/M_m)$; summing yields the claimed identity.

**Key facts.** `FABL.totalInfluence_gotsmanLinialExtremizer`, `FABL.oddMajorityInfluence_pos`.
