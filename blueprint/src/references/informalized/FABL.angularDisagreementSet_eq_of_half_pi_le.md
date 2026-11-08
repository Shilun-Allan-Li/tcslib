<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/NoiseStability/GaussianDisagreement.lean :: FABL.angularDisagreementSet_eq_of_half_pi_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Angular disagreement intervals

**Claim.** For $\pi/2\leq\alpha\leq\pi$, the angles $\theta\in(-\pi,\pi)$ for which $\cos\theta\cos(\theta-\alpha)<0$ form $(-\pi,\alpha-3\pi/2)\cup(-\pi/2,\alpha-\pi/2)\cup(\pi/2,\pi)$.

**Proof.** On $(-\pi,\pi)$, cosine is positive exactly on $(-\pi/2,\pi/2)$ and negative on the two outer intervals (`cos_pos_iff_of_neg_pi_lt_of_lt_pi`, `cos_neg_iff_of_neg_pi_lt_of_lt_pi`). Since $\alpha\in[\pi/2,\pi]$ and $\theta\in(-\pi,\pi)$, the shifted angle $\theta-\alpha$ lies in $(-2\pi,\pi)$. On this larger range, cosine is positive for angles below $-3\pi/2$ or between $-\pi/2$ and $\pi/2$, and negative between $-3\pi/2$ and $-\pi/2$ or above $\pi/2$ (`cos_pos_iff_of_neg_two_pi_lt_of_lt_pi`, `cos_neg_iff_of_neg_two_pi_lt_of_lt_pi`).

The product is negative precisely when the two cosine factors have opposite signs. If $\cos\theta>0$, then $\theta\in(-\pi/2,\pi/2)$; the shifted cosine can be negative only when $\theta-\alpha\in(-3\pi/2,-\pi/2)$, which gives $\theta\in(-\pi/2,\alpha-\pi/2)$. If $\cos\theta<0$, then either $\theta\in(-\pi,-\pi/2)$ or $\theta\in(\pi/2,\pi)$. In the first interval, opposite signs require $\theta-\alpha<-3\pi/2$, giving $\theta\in(-\pi,\alpha-3\pi/2)$; in the second they require $\theta-\alpha\in(-\pi/2,\pi/2)$, giving $\theta\in(\pi/2,\pi)$. Conversely, on each of these three intervals the same sign descriptions show that the cosine factors have opposite signs. The strict inequalities exclude the endpoints, where one factor can vanish.

**Key facts.** `FABL.cos_pos_iff_of_neg_pi_lt_of_lt_pi`, `FABL.cos_neg_iff_of_neg_pi_lt_of_lt_pi`, `FABL.cos_pos_iff_of_neg_two_pi_lt_of_lt_pi`, `FABL.cos_neg_iff_of_neg_two_pi_lt_of_lt_pi`.
