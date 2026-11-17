<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Jacobi.lean :: Complexity.BinArith.jacobiModAlg_pairEncode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Jacobi symbol modulo an odd integer

**Claim.** For natural numbers $a,n$ with $n$ odd, applying the modular Jacobi algorithm to the pairing of their binary expansions yields the binary expansion of the least nonnegative residue of the Jacobi symbol $(a/n)$ modulo $n$.

**Proof.** Substitute the binary-encoding correctness result for the Jacobi algorithm, then decode the pair and evaluate the binary expansions. The additions, subtractions, and final remainder in the modular algorithm consequently reduce to the integer expression $(\operatorname{jacobiSym}(a,n)+1-1)\bmod n$, with the symbol viewed as an integer. The Jacobi symbol is one of $-1,0,1$. For value $1$ the residue is $1\bmod n$; for value $0$ it is $0$; and for value $-1$, use $-1=(n-1)-n$ to see that its residue is $n-1$. Since oddness gives $n\ge1$, these are the least nonnegative residues. Thus the resulting natural number, and hence its binary expansion, is the required residue.

**Key facts.** `Complexity.BinArith.jacobiAlg_pairEncode`, `Complexity.BinArith.add_pairEncode`, `Complexity.pairSndD_pairEncode`, `Complexity.pairFstD_pairEncode`, `Complexity.LogProg.bitsVal_bits`.
