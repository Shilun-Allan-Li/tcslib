<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/BLR/ZkBLR.lean :: ZkBLR.BLR_soundness -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# BLR soundness over prime fields

**Claim.** For a normalized function on $\mathbb Z_p^n$ that is $\varepsilon$-far from every linear function, the BLR acceptance probability is at most $1-\frac{p-1}{p}(1-\cos(2\pi/p))\varepsilon$.

**Proof.** Use the Fourier representation of the acceptance probability (`ZkBLR.BLR_accept_prob_eq_fourier_sum`) and separate the twist $j=0$ from the nonzero twists. The zero twist contributes exactly $1$ (`ZkBLR.lift_omega_j_zero_contribution`). For each nonzero twist, the distance hypothesis bounds its weighted Fourier sum by $1-(1-\cos(2\pi/p))\varepsilon$ (`ZkBLR.weighted_sum_lift_omega_j_bound`). There are $p-1$ such twists. Averaging these contributions with factor $1/p$ gives $\frac1p(1+(p-1)(1-(1-\cos(2\pi/p))\varepsilon))$, which simplifies to the asserted bound.

**Key facts.** `ZkBLR.BLR_accept_prob_eq_fourier_sum`, `ZkBLR.lift_omega_j_zero_contribution`, `ZkBLR.weighted_sum_lift_omega_j_bound`.
