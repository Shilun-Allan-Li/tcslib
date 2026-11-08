<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/BLR/ZkFourier.lean :: ZkFourier.card_ZkVec -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cardinality of the vector space

**Claim.** For $k\ge1$, the set $(\mathbb{Z}/k\mathbb{Z})^n$ is finite and has cardinality $k^n$.

**Proof.** A vector in $(\mathbb{Z}/k\mathbb{Z})^n$ is a function from the $n$ coordinate positions to $\mathbb{Z}/k\mathbb{Z}$. Each position has $k$ possible values, independently of the others, so the number of such functions is the product of $n$ copies of $k$, namely $k^n$.
