<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/BLR/ZkBLR.lean :: ZkBLR.re_fourier_coeff_lift_omega_j_unit_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unit-Twisted Fourier Bound

**Claim.** If $f$ is normalized and $\varepsilon$-far from linear, then twisting its lift by any unit $j$ preserves the real-part Fourier coefficient bound $1-(1-\cos(2\pi/k))\varepsilon$.

**Proof.** Define $g(x)=j f(x)$. The unit-scaling farness lemma says that $g$ remains normalized and $\varepsilon$-far from linear. The lift of $g$ is precisely the $j$-twisted lift of $f$. Applying the ordinary Fourier bound to $g$ at frequency $s$ yields the asserted inequality.

**Key facts.** `ZkBLR.unit_mul_epsilon_far`, `ZkBLR.re_epsilon_far_bounds_fourier`.
