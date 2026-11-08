<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/GaussianPolar.lean :: BooleanAnalysis.ThresholdFunctions.cos_nonpos_iff_of_le_neg_pi_div_two -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cosine sign on a negative angular interval

**Claim.** If $-2\pi<u\le-\pi/2$, then $\cos u\le0$ if and only if $-3\pi/2\le u$.

**Proof.** Suppose first that $\cos u\le0$ but $u<-3\pi/2$. Then $u+2\pi$ lies strictly between $0$ and $\pi/2$, where cosine is positive. Periodicity gives $\cos(u+2\pi)=\cos u$, contradicting the assumed nonpositivity. Hence $u\ge-3\pi/2$. Conversely, if $-3\pi/2\le u\le-\pi/2$, then $-u\in[\pi/2,3\pi/2]$, where cosine is nonpositive. Since cosine is even, $\cos u=\cos(-u)\le0$.
