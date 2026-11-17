<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/BLR/ZkBLR.lean :: ZkBLR.geom_sum_toOmega_dual -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Dual geometric sum

**Claim.** For every residue class $a\in\mathbb Z/k\mathbb Z$, the sum of the characters $j\mapsto\omega_k^{ja}$ is $k$ when $a=0$ and $0$ otherwise.

**Proof.** Commutativity of multiplication in $\mathbb Z/k\mathbb Z$ rewrites each summand $\omega_k^{ja}$ as $\omega_k^{aj}$. The geometric-sum identity for a fixed multiplier then gives $k$ if that multiplier is zero and $0$ otherwise (\texttt{ZkFourier.geom\_sum\_toOmega}).

**Key facts.** `ZkFourier.geom_sum_toOmega`.
