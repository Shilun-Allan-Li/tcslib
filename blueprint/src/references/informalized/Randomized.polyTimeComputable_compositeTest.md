<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Primality.lean :: Randomized.polyTimeComputable_compositeTest -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Composite Test

**Claim.** The function sending each bit string $z$ to the singleton list containing the stated composite test result is polynomial-time computable.

**Proof.** Decode the first component of $z$ and normalize its represented integer by taking its binary bits; this is polynomial-time computable. Also form $u$ by appending three $1$ bits to that component. Pairing $u$ with the decoded second component and taking the length-sized prefix computes the first block used by the test. To obtain the next block, first remove that prefix from the second component, pair the suffix with $u$, and take its length-sized prefix. Each of these operations is polynomial-time computable by closure under composition, pairing, appending a constant, and prefix-taking. Pair the normalized integer with the constant representation of $2$ and test first whether it is less than $2$, then whether it equals $2$. If neither condition holds, test whether the first component's least significant bit is zero. In the remaining branch, apply the polynomial-time liar-round test to each of the two formed blocks, conjoin the results, and negate. Polynomial-time computability is preserved by Boolean negation, conjunction, and conditional selection, so the nested case distinction computes the required singleton output in polynomial time.

**Key facts.** `Complexity.polyTimeComputable_pairFstD`, `Complexity.BinArith.polyTimeComputable_normBits`, `Complexity.PolyTimeComputable.append`, `Complexity.polyTimeComputable_const`, `Complexity.PolyTimeComputable.pairEncode`, `Complexity.polyTimeComputable_pairSndD`, `Randomized.polyTimeComputable_takePrefixByLen`, `Randomized.polyTimeComputable_dropPrefixByLen`, `Complexity.BinArith.polyTimeComputable_lt`, `Complexity.BinArith.polyTimeComputable_beq`, `Complexity.polyTimeComputable_ite`, `Complexity.polyTimeComputable_headD`, `Complexity.polyTimeComputable_not`, `Complexity.polyTimeComputable_and`, `Randomized.polyTimeComputable_liarRound`.
