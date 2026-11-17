<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/BLR/ZkBLR.lean :: ZkBLR.re_toOmega_le_re_rootOfUnity -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Real Part of a Nontrivial Root

**Claim.** For $k\ge2$ and nonzero $a\in\mathbb Z/k\mathbb Z$, the real part of $\omega_k^a$ is at most $\cos(2\pi/k)$.

**Proof.** The canonical representative satisfies $1\le a.val\le k-1$. Consequently its angle $\theta=2\pi a.val/k$ lies between $2\pi/k$ and $2\pi-2\pi/k$. If $\theta\le\pi$, cosine is decreasing on $[0,\pi]$, so $\cos\theta\le\cos(2\pi/k)$. If $\theta>\pi$, use $\cos\theta=\cos(2\pi-\theta)$. The reflected angle is nonnegative and at most $\pi-2\pi/k$, hence at most $\pi$; it is also at least $2\pi/k$. Monotonicity on $[0,\pi]$ again gives the bound. Finally, the real part of $\omega_k^a=e^{i\theta}$ is $\cos\theta$.
