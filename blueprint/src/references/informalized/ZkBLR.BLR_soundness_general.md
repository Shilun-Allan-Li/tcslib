<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/BLR/ZkBLR.lean :: ZkBLR.BLR_soundness_general -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# BLR soundness over residue rings

**Claim.** For $k\ge2$, a normalized function on $\mathbb Z_k^n$ that is $\varepsilon$-far from every linear function has BLR acceptance probability at most $1-\frac{\varphi(k)}{k}(1-\cos(2\pi/k))\varepsilon$.

**Proof.** Express the acceptance probability as the Fourier sum over twists, with its factor $1/k$ (`ZkBLR.BLR_accept_prob_eq_fourier_sum`). Partition the twists into units and nonunits. Each unit twist satisfies the stronger bound $1-(1-\cos(2\pi/k))\varepsilon$ (`ZkBLR.weighted_sum_unit_bound`), and there are $\varphi(k)$ units. Each nonunit twist contributes at most $1$ (`ZkBLR.weighted_fourier_sum_le_one`), and there are $k-\varphi(k)$ nonunits. Thus the full sum is at most $\varphi(k)(1-c\varepsilon)+(k-\varphi(k))$, where $c=1-\cos(2\pi/k)$. Dividing by $k$ and simplifying gives the claimed inequality.

**Key facts.** `ZkBLR.BLR_accept_prob_eq_fourier_sum`, `ZkBLR.weighted_fourier_sum_le_one`, `ZkBLR.weighted_sum_unit_bound`.
