<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Jacobi.lean :: Complexity.BinArith.jacMeasure_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Decrease of the Jacobi measure

**Claim.** For bit strings $A,N,s$ with the integer represented by $N$ odd, a positive Jacobi measure strictly decreases after one Jacobi step, while measure zero makes the step leave the encoding unchanged.

**Proof.** First consider $A$ representing zero. The Jacobi step fixes the encoded state, and the measure is zero: its product term vanishes, while the extra indicator is zero because $N$ is positive. Thus the claimed decrease implication is vacuous and the fixed-state assertion holds. Now suppose $A$ is positive. Since $N$ is odd it is positive too, so their product $P$ is positive. The zero-measure case is impossible: the positive product has positive binary size, hence the measure is positive. For the decrease claim, split according to whether $A$ is odd. If it is odd, the step replaces the product $AN$ by $(N\bmod A)A$. This product is at most $AN$, so its binary size does not increase. When $N\le A$, the extra indicator can be one, but the strict decrease in size follows from the bound by the original product and the measure's original size contribution; when $N>A$, the old indicator is zero, and division with remainder gives $2A(N\bmod A)\le AN$, so the new binary size is strictly smaller. If $A$ is even, the step halves it, replacing the product by $(A/2)N$. The identity that removing the first bit divides the represented integer by two, together with evenness, gives $2(A/2)N=AN$. Therefore its binary size strictly decreases. The new indicator is no larger than the old one, since $N\le A/2$ implies $N\le A$. Combining these bounds proves strict decrease of the whole measure.

**Key facts.** `Complexity.pairFstD_pairEncode`, `Complexity.pairSndD_pairEncode`, `Complexity.BinArith.bitsVal_drop_one`, `Complexity.BinArith.bitsVal_mod_two`, `Complexity.BinArith.size_lt_of_two_mul_le`.
