<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/BLR/ZkBLR.lean :: ZkBLR.re_fourier_coeff_lift_omega_j_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Twisted Fourier Coefficient Bound

**Claim.** For prime $p$, if $f$ is normalized and $\varepsilon$-far from linear, then for every nonzero $j\in\mathbb Z/p\mathbb Z$ and every frequency $s$, the real part of the Fourier coefficient of the $j$-twisted lift is at most $1-(1-\cos(2\pi/p))\varepsilon$.

**Proof.** Set $g(x)=j f(x)$. Since $j$ is nonzero modulo the prime $p$, it is invertible. Multiplication by $j$ preserves normalization, and it preserves distance from the set of linear maps: for any linear $g'$, compare $j f$ with $g'$ pointwise by multiplying both values by $j^{-1}$, so their disagreement set is that of $f$ and $j^{-1}g'$. The map $j^{-1}g'$ is linear, hence the farness of $f$ implies that of the scaled function $g$. Apply the Fourier bound for ordinary lifts to $g$. Its lift is exactly the $j$-twisted lift of $f$, giving the desired inequality.

**Key facts.** `ZkBLR.re_epsilon_far_bounds_fourier`.
