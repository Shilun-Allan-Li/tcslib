<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/NoiseStability/GaussianDisagreement.lean :: FABL.angularDisagreementSet_eq_of_le_half_pi -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Angular disagreement intervals

**Claim.** For $0\leq\alpha\leq\pi/2$, the angles $\theta\in(-\pi,\pi)$ for which $\cos\theta\cos(\theta-\alpha)<0$ form $(-\pi/2,\alpha-\pi/2)\cup(\pi/2,\alpha+\pi/2)$.

**Proof.** For $\theta\in(-\pi,\pi)$, cosine is positive on $(-\pi/2,\pi/2)$ and negative on the two outer intervals (`cos_pos_iff_of_neg_pi_lt_of_lt_pi`, `cos_neg_iff_of_neg_pi_lt_of_lt_pi`). Also $\theta-\alpha\in(-2\pi,\pi)$, where the signs of cosine are given by `cos_pos_iff_of_neg_two_pi_lt_of_lt_pi` and `cos_neg_iff_of_neg_two_pi_lt_of_lt_pi`.

If $\cos\theta>0$, then $\theta\in(-\pi/2,\pi/2)$. Opposite signs require $\cos(\theta-\alpha)<0$, which on the relevant shifted range means $\theta-\alpha<-\pi/2$; hence $\theta\in(-\pi/2,\alpha-\pi/2)$. If $\cos\theta<0$, then $\theta$ lies in one of the outer intervals. For $\theta\in(-\pi,-\pi/2)$, the shifted angle is below $-\pi/2$ and its cosine is negative, so the factors cannot have opposite signs. For $\theta\in(\pi/2,\pi)$, the shifted cosine is positive exactly when $\theta-\alpha<\pi/2$, giving $\theta\in(\pi/2,\alpha+\pi/2)$. Conversely, each of the two stated intervals has the required opposite signs, proving the set equality.

**Key facts.** `FABL.cos_pos_iff_of_neg_pi_lt_of_lt_pi`, `FABL.cos_neg_iff_of_neg_pi_lt_of_lt_pi`, `FABL.cos_pos_iff_of_neg_two_pi_lt_of_lt_pi`, `FABL.cos_neg_iff_of_neg_two_pi_lt_of_lt_pi`.
