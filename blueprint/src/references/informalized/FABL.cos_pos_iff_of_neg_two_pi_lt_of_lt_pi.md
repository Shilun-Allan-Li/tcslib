<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/NoiseStability/GaussianDisagreement.lean :: FABL.cos_pos_iff_of_neg_two_pi_lt_of_lt_pi -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positive Cosine on an Extended Interval

**Claim.** If $-2\pi<x<\pi$, then $\cos x>0$ exactly when $x<-3\pi/2$ or $-\pi/2<x<\pi/2$.

**Proof.** First suppose $x<-\pi$. Periodicity gives $\cos x=\cos(x+2\pi)$, with $-\pi<x+2\pi<\pi$. The principal-interval characterization (`FABL.cos_pos_iff_of_neg_pi_lt_of_lt_pi`) says positivity is equivalent to $-\pi/2<x+2\pi<\pi/2$. Under $x<-\pi$, this is equivalent to $x<-3\pi/2$. If $x=-\pi$, cosine is $-1$, and neither stated alternative holds. In the remaining case $x>-\pi$, apply the principal-interval characterization directly. Its interval condition is exactly $-\pi/2<x<\pi/2$; the alternative $x<-3\pi/2$ is impossible in this case.

**Key facts.** `FABL.cos_pos_iff_of_neg_pi_lt_of_lt_pi`.
