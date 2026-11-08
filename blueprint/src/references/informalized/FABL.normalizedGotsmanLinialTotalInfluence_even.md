<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/GotsmanLinialExtremizer.lean :: FABL.normalizedGotsmanLinialTotalInfluence_even -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Even-Dimension Influence Identity

**Claim.** For $k>0$, the normalized total influence of the Gotsman–Linial extremizer on the $(k+2m)$-dimensional cube equals $\sqrt{k+2m}\,M_m\sum_{j=0}^{k-1}Q_{m,k-1,j}/M_m$.

**Proof.** Set $N=k+2m$. Since $k>0$, $N>0$, so $\sqrt N>0$. The starting index in the extremizer’s binomial formula is $\lfloor(N-k)/2\rfloor=m$, and its top binomial index satisfies $N-1=2m+(k-1)$. The total-influence formula for the Gotsman–Linial extremizer (`totalInfluence_gotsmanLinialExtremizer`) thus expresses its total influence as $N/2^{N-1}$ times the sum, for $0\le j<k$, of $\binom{2m+k-1}{m+j}$. By definition, each such binomial coefficient divided by $2^{2m+k-1}$ is $Q_{m,k-1,j}$, while $M_m=\binom{2m}{m}/2^{2m}$ is positive (`oddMajorityInfluence_pos`). Substituting these expressions and dividing by $\sqrt N$ gives the desired form: each term is rearranged as $\sqrt N\,M_m(Q_{m,k-1,j}/M_m)$. Positivity of $M_m$ and $\sqrt N$ justifies the divisions; the remaining equality is algebra.

**Key facts.** `FABL.totalInfluence_gotsmanLinialExtremizer`, `FABL.oddMajorityInfluence_pos`.
