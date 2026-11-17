<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/EXP.lean :: Complexity.enumCandidates_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exact-Width Words and Bounded Ranks

**Claim.** There is a word of length $w$ satisfying $p$ exactly when the width-$w$ little-endian binary word of some rank $i<2^w$ satisfies $p$.

**Proof.** Given a word $u$ of length $w$, take its binary rank. That rank is less than $2^{|u|}$ (`Complexity.enumValue_lt`), hence less than $2^w$, and the completeness property of the encoding (`Complexity.enumWord_complete`) recovers $u$ from that rank. Conversely, any rank below $2^w$ yields an encoded word of length $w` (`Complexity.enumWord_length`), so if that word satisfies $p$, it is the required witness.

**Key facts.** `Complexity.enumValue_lt`, `Complexity.enumWord_complete`, `Complexity.enumWord_length`.
