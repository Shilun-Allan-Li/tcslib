<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/NoiseStability/GaussianDisagreement.lean :: FABL.cos_neg_iff_of_neg_pi_lt_of_lt_pi -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Negative Cosine on a Principal Interval

**Claim.** If $-\pi<x<\pi$, then $\cos x<0$ exactly when $x<-\pi/2$ or $x>\pi/2$.

**Proof.** For the forward implication, if neither strict inequality holds, then $-\pi/2\le x\le\pi/2$. Cosine is nonnegative throughout this interval, contradicting $\cos x<0$. Conversely, if $x<-\pi/2$, then the given lower bound $x> -\pi$ places $-x$ strictly between $\pi/2$ and $\pi$; cosine is negative there, and $\cos x=\cos(-x)$. If instead $x>\pi/2$, the upper bound $x<\pi$ puts $x$ directly in the interval where cosine is negative.
