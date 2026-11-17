<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Loops.lean :: Complexity.BinArith.eqW_pairEncode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Equality Test on Paired Bit Strings

**Claim.** For any bit strings $a$ and $b$, the equality test applied to their pair encoding returns true exactly when $a=b$.

**Proof.** The pair encoding decodes back to its two components, so the test compares the lengths of $a,b$ and their bit values. If $a=b$, both comparisons succeed. If $a\ne b$, the conjunction can be true only if the lengths and bit values agree; but equal lengths together with equal bit values force the strings to be equal (Complexity.LogProg.eq_of_bitsVal_eq). This contradicts $a\ne b$, so the test is false.

**Key facts.** `Complexity.pairFstD_pairEncode`, `Complexity.pairSndD_pairEncode`, `Complexity.LogProg.eq_of_bitsVal_eq`.
