<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Parse.lean :: Complexity.Codec.bitsVal_le_of_width -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binary Value Bound from Width

**Claim.** If $L$ is positive and the length of a Boolean list $w$ is at most the length of the binary expansion of $L$, then for every $i$ the binary value of the list obtained by dropping the first $i$ bits of $w$ is at most $2L$.

**Proof.** The value of any Boolean list is strictly less than two raised to its length (`bitsVal_lt_two_pow`). Dropping entries cannot increase the length, so the value of the resulting list is less than or equal to $2$ raised to the length of the binary expansion of $L$. For positive $L$, that power is at most $2L$: the binary expansion has length equal to the binary size of $L$, and the defining size bounds place $L$ at least at the corresponding lower power of two. Combining these inequalities gives the claimed bound.

**Key facts.** `Complexity.Codec.bitsVal_lt_two_pow`.
