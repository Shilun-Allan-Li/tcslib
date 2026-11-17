<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/PrimalityMath.lean :: Randomized.jacobiSymZMod_mul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Multiplicativity of the Jacobi Symbol

**Claim.** For every positive natural number $N$ and residue classes $x,y$ modulo $N$, the Jacobi symbol viewed as a residue class modulo $N$ is multiplicative: its value at $xy$ equals the product of its values at $x$ and $y$.

**Proof.** By definition, each value is obtained by taking the integer Jacobi symbol of the canonical representative and reducing it modulo $N$. The integer Jacobi symbol is multiplicative in its first argument, so the symbol at the product of the representatives is the product of their symbols. Reduction from the integers to $\mathbb Z/N\mathbb Z$ preserves multiplication. The representative of the product $xy$ is congruent modulo $N$ to the product of the representatives; the Jacobi symbol is periodic in its first argument modulo $N$, so replacing that product by the canonical representative does not change the resulting residue class.
