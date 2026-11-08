<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Primality.lean :: Randomized.liarRound_pairEncode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Euler Liar Round Correctness

**Claim.** For an odd natural number $N>1$ and a finite bit string $w$, the liar-round test on the encoding of the binary expansion of $N$ paired with $w$ is true exactly when $A=1+\operatorname{bitsVal}(w)\bmod(N-1)$ is coprime to $N$ and its Jacobi symbol modulo $N$ equals $A^{(N-1)/2}$ in $\mathbb Z/N\mathbb Z$.

**Proof.** First, simplify the arithmetic performed by the encoded test. The subtraction routine applied to the encoding of $N$ and $1$ yields the binary expansion of $N-1$. The addition routine, with the remainder of the value of $w$ modulo $N-1$, yields the binary expansion of $A=1+\operatorname{bitsVal}(w)\bmod(N-1)$. These identifications use the fact that binary encoding preserves value (`Complexity.LogProg.bitsVal_bits`) and that pairing can be decoded back into its two lists (`Complexity.pairFstD_pairEncode`, `Complexity.pairSndD_pairEncode`).

Next, the exponentiation routine applied to the relevant encodings yields the binary expansion of $A^{(N-1)/2}\bmod N$. Here the value of the exponent is obtained from the binary list with its first bit dropped: dropping that bit divides the represented value by two (`Complexity.BinArith.bitsVal_drop_one`). Since $N$ is odd and greater than one, this gives the stated exponent and a nonzero modulus. The gcd routine likewise returns the binary expansion of $\gcd(A,N)$ (`Complexity.BinArith.gcd_pairEncode`), while the Jacobi computation returns the binary expansion of the natural-number representative of the Jacobi symbol modulo $N$ (`Complexity.BinArith.jacobiModAlg_pairEncode`).

With these computations substituted, the Boolean test is true precisely when $\gcd(A,N)=1$ and the two residues agree. The arithmetic characterization of the Euler-liar predicate says that this is equivalent to coprimality and equality of the Jacobi-symbol remainder with the natural-number power remainder (`Randomized.isEulerLiar_iff_emod`). The Jacobi-symbol remainder is nonnegative because the modulus is nonzero, so its integer remainder can be identified with its natural-number representative. Thus the test agrees with the decision of the stated predicate.

**Key facts.** `Complexity.LogProg.bitsVal_bits`, `Complexity.pairFstD_pairEncode`, `Complexity.pairSndD_pairEncode`, `Complexity.BinArith.bitsVal_drop_one`, `Complexity.BinArith.gcd_pairEncode`, `Complexity.BinArith.jacobiModAlg_pairEncode`, `Randomized.isEulerLiar_iff_emod`.
