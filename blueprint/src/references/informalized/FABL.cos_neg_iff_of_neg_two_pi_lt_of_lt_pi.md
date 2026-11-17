<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/NoiseStability/GaussianDisagreement.lean :: FABL.cos_neg_iff_of_neg_two_pi_lt_of_lt_pi -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Negative Cosine on an Extended Interval

**Claim.** If $-2\pi<x<\pi$, then $\cos x<0$ exactly when $-3\pi/2<x<-\pi/2$ or $x>\pi/2$.

**Proof.** Split according to whether $x<-\pi$. In that case, periodicity gives $\cos x=\cos(x+2\pi)$, and the hypotheses place $x+2\pi$ strictly between $-\pi$ and $\pi$. The principal-interval characterization (`FABL.cos_neg_iff_of_neg_pi_lt_of_lt_pi`) now applies. Translating its alternatives back by $2\pi$ gives precisely the stated interval $-3\pi/2<x<-\pi/2$; its other alternative is incompatible with $x<-\pi$. If $x=-\pi$, cosine equals $-1$, and this point lies in the stated negative interval. In the remaining case, $x>-\pi$, so the principal-interval characterization applies directly: its left alternative gives $-3\pi/2<x<-\pi/2$, while its right alternative gives $x>\pi/2$.

**Key facts.** `FABL.cos_neg_iff_of_neg_pi_lt_of_lt_pi`.
