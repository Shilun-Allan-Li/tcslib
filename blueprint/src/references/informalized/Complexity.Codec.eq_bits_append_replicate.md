<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Word.lean :: Complexity.Codec.eq_bits_append_replicate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binary expansion with zero padding

**Claim.** Every finite Boolean list is the least-significant-first binary expansion of its value, followed by enough false entries to restore its original length.

**Proof.** Proceed by induction on the list. The empty list has value zero, whose binary expansion is empty, so the assertion holds. For a list $b::w$, the induction hypothesis says that $w$ is the binary expansion of its value followed by false entries. Its length also implies that the unpadded binary expansion of that value has length at most $|w|$. If the value of $w$ is zero and $b$ is false, the whole list represents zero; the induction hypothesis then shows that it consists entirely of false entries, exactly the padding required for zero. Otherwise, the binary expansion identity for $2n+b$ says that its digits are $b$ followed by the digits of $n$, provided that $n=0$ forces $b$ to be true. That condition holds here: if $n=0$ and $b$ were false, we would be in the excluded case. Thus the first digit is $b$, and the remaining digits with their padding are precisely those supplied by the induction hypothesis. The length calculation shows that the required padding after the first digit has the same length as the padding for $w$, completing the induction.

**Key facts.** `Complexity.LogProg.bits_two_mul_add`.
