<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/PrimalityMath.lean :: Randomized.qrSymbol_eq_legendreSym -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Quadratic Symbol and Legendre Symbol

**Claim.** For a prime $p$ and any natural number $A$, the quadratic residue symbol modulo $p$ equals the Legendre symbol $\left(\frac{A}{p}\right)$.

**Proof.** Because $p$ is prime, coprimality of $A$ and $p$ is equivalent to the residue of $A$ in $\mathbb{Z}/p\mathbb{Z}$ being nonzero. If they are coprime, the quadratic residue symbol is $1$ when that residue is a square and $-1$ when it is not. The Legendre symbol has exactly these respective values, by its square and nonsquare characterizations. If they are not coprime, the residue of $A$ is zero; the quadratic residue symbol is then $0$, as is the Legendre symbol by its zero criterion. These cases give the equality.

**Key facts.** `Randomized.coprime_iff_natCast_ne_zero`.
