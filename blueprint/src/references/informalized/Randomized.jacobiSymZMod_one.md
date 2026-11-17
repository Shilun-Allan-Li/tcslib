<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/PrimalityMath.lean :: Randomized.jacobiSymZMod_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Jacobi Symbol at One

**Claim.** For every positive natural number $N$, the Jacobi symbol modulo $N$, viewed as a residue class in $\mathbb Z/N\mathbb Z$, takes the value $1$ at the multiplicative identity.

**Proof.** Apply the natural-cast formula for the Jacobi symbol to $A=1$; the residue class of the natural number $1$ is the multiplicative identity. The integer Jacobi symbol of $1$ is $1$, so its residue class modulo $N$ is also the identity.

**Key facts.** `Randomized.jacobiSymZMod_natCast`.
