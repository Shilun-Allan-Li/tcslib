<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/ModPow.lean :: Complexity.BinArith.gcd_pairEncode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gcd of Encoded Binary Numbers

**Claim.** For all natural numbers $a,b$, applying the bit-string gcd operation to the self-delimiting encoding of their binary expansions yields the binary expansion of $\gcd(a,b)$.

**Proof.** The pair encoding decodes to its original two components (`Complexity.pairFstD_pairEncode`, `Complexity.pairSndD_pairEncode`). Thus the gcd operation on this encoding takes the gcd of the values represented by $\operatorname{Nat.bits}(a)$ and $\operatorname{Nat.bits}(b)$. Each of those values is its original natural number (`Complexity.LogProg.bitsVal_bits`), so the result is precisely the binary expansion of $\gcd(a,b)$.

**Key facts.** `Complexity.LogProg.bitsVal_bits`.
