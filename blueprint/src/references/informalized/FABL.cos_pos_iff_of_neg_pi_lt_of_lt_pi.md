<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/NoiseStability/GaussianDisagreement.lean :: FABL.cos_pos_iff_of_neg_pi_lt_of_lt_pi -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positive Cosine on a Principal Interval

**Claim.** If $-\pi<x<\pi$, then $\cos x>0$ exactly when $-\pi/2<x<\pi/2$.

**Proof.** If $\cos x>0$, then $x$ cannot be at or below $-\pi/2$: in that range, the hypotheses put $-x$ between $\pi/2$ and $\pi$, where cosine is nonpositive, and $\cos x=\cos(-x)$. Nor can $x$ be at or above $\pi/2$, where cosine is nonpositive directly. Thus $-\pi/2<x<\pi/2$. Conversely, cosine is positive on the open interval $(-\pi/2,\pi/2)$, giving the claim.
