<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/StableHypercubeExplicit.lean :: FABL.noisyHypercubeUndirectedEdgeWeight_eq_hamming -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Noisy Edge Weight Formula

**Claim.** For noise parameter δ in [0,1], the undirected edge weight between x and y equals 2^(1−n) times δ to the Hamming distance between x and y, times (1−δ) to the remaining number of coordinates.

**Proof.** By the undirected-weight identity (`stableHypercubeUndirectedEdgeWeight_eq_two_mul`), the undirected weight is twice the directed weight from x to y. The directed weight factors as the uniform probability of x times the transition probability from x to y (`stableHypercubeEdgeWeight_eq_uniform_mul_transition`). Under the specialization ρ = 1−2δ, the transition probability is δ^{hammingDist(x,y)}(1−δ)^{n−hammingDist(x,y)} (`noiseKernel_noisy_apply_toReal`). Since x is uniform on the sign cube, its probability is 2^{−n}; multiplying by two gives the stated factor 2^{1−n}.

**Key facts.** `FABL.stableHypercubeUndirectedEdgeWeight_eq_two_mul`, `FABL.stableHypercubeEdgeWeight_eq_uniform_mul_transition`, `FABL.noiseKernel_noisy_apply_toReal`.
