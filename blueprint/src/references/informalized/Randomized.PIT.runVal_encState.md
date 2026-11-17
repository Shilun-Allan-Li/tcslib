<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZeroPRun.lean :: Randomized.PIT.runVal_encState -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Value Extracted from an Encoded State

**Claim.** For bit strings $ctx,w$ and a finite list $vs$ of natural numbers, value extraction on their encoded state yields the binary expansion of the entry at index $|vs|-1$, using truncated subtraction and returning zero when that index is out of range.

**Proof.** The pair projections in the encoded state simplify the index field to the unary string of length one less than $|vs|$, and the stored-value field to the encodings of the binary expansions of the entries of $vs$. The lookup identity for `getW` on such a pair encoding says that it returns the binary expansion of the stored entry at the index specified by the unary string, with zero as the default when lookup is out of range. Here that index is $|vs|-1$, as claimed.

**Key facts.** `Complexity.pairFstD_pairEncode`, `Complexity.pairSndD_pairEncode`, `Complexity.BinArith.getW_pairEncode_bits`.
