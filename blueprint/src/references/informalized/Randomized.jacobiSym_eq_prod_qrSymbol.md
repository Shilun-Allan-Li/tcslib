<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/PrimalityMath.lean :: Randomized.jacobiSym_eq_prod_qrSymbol -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Jacobi Symbol as a Product of Quadratic Symbols

**Claim.** For natural numbers $A,N$, the Jacobi symbol $(A/N)$ is the product, over the prime factors of $N$, of the quadratic-residue symbols evaluated at $A$.

**Proof.** Unfold the definition of the Jacobi symbol as the product of Legendre symbols over the prime factor list of $N$. It remains to identify each factor with the corresponding quadratic-residue symbol. For a prime $p$, the quadratic-residue symbol at $A$ equals the Legendre symbol at $A$ (\texttt{Randomized.qrSymbol_eq_legendreSym}). Apply this identification to the first prime factor and use induction on the remaining list: the product for the tail agrees by the induction hypothesis, while the first factors agree by the prime case. The empty factor list gives the equality of empty products.

**Key facts.** `Randomized.qrSymbol_eq_legendreSym`.
