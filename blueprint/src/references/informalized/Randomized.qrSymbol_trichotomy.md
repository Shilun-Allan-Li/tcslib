<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/PrimalityMath.lean :: Randomized.qrSymbol_trichotomy -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Quadratic Symbol Trichotomy

**Claim.** For any natural numbers $N$ and $A$, the quadratic residue symbol is one of $0$, $1$, or $-1$.

**Proof.** By definition, if $A$ is not coprime to $N$, the symbol is $0$. If they are coprime, the residue of $A$ is either a square or not: in the first case the symbol is $1$, and in the second it is $-1$. Thus one of the three asserted equalities holds.
