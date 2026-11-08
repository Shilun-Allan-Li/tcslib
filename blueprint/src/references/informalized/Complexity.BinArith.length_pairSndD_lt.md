<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Words.lean :: Complexity.BinArith.length_pairSndD_lt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Strict decrease under second projection

**Claim.** For every nonempty bit string $w$, the total second projection of $w$ has length strictly less than $|w|$.

**Proof.** Split according to whether parsing $w$ succeeds. If it fails, the total second projection is the empty string, whose length is strictly less than the positive length of nonempty $w$. If parsing succeeds with components $a,b$, then $w$ is exactly their pair encoding (`Turing.eq_pairEncode_of_pairDecode`). The total second projection of a pair encoding is its second component (`Complexity.pairSndD_pairEncode`), and the pair encoding length formula (`Turing.length_pairEncode`) says $|w|=2|a|+2+|b|$. This is strictly greater than $|b|$, as required.

**Key facts.** `Turing.eq_pairEncode_of_pairDecode`, `Complexity.pairSndD_pairEncode`, `Turing.length_pairEncode`.
