<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Jacobi.lean :: Complexity.BinArith.jacobiAlg_pairEncode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Jacobi algorithm on encoded integers

**Claim.** For natural numbers $a,n$ with $n$ odd, applying the Jacobi algorithm to the pair encoding of their binary expansions yields the binary expansion of $(\operatorname{jacobiSym}(a,n)+1).toNat$.

**Proof.** Apply correctness of the Jacobi algorithm to the encoding of the two binary expansions. The pair encoding's second projection is the binary expansion of $n$, whose represented value is $n$; hence it is odd by hypothesis. The algorithm therefore returns the binary encoding of one plus the Jacobi symbol of the represented projections. Each projection represents its original number, so this is exactly the asserted binary expansion.

**Key facts.** `Complexity.BinArith.jacobiAlg_eq`, `Complexity.LogProg.bitsVal_bits`.
