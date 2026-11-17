<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/BLR/ZkBLR.lean :: ZkBLR.weighted_fourier_sum_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Weighted Fourier Sum Bound

**Claim.** For prime $p$, if $f$ is normalized and $\varepsilon$-far from linear, then the sum of $|\widehat{\widetilde f}(s)|^2\operatorname{Re}(\widehat{\widetilde f}(s))$ over all frequencies is at most $1-(1-\cos(2\pi/p))\varepsilon$.

**Proof.** For each frequency, the real-part Fourier bound gives $\operatorname{Re}(\widehat{\widetilde f}(s))\le 1-(1-\cos(2\pi/p))\varepsilon$. Multiplying by the nonnegative weight $|\widehat{\widetilde f}(s)|^2$ preserves the inequality, and summing gives an upper bound equal to that common right-hand factor times the sum of the weights. Parseval's identity for the unit-modulus lift says this sum is $1$. The stated bound follows.

**Key facts.** `ZkBLR.re_epsilon_far_bounds_fourier`, `ZkBLR.parseval_lift_omega`.
