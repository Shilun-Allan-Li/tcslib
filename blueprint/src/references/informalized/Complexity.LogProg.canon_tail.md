<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/FragDec.lean :: Complexity.LogProg.canon_tail -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Canonicality Passes to the Tail

**Claim.** If a word formed by prepending one bit $b$ to $w$ is canonical, then $w$ is canonical.

**Proof.** Take any proof that $w$ is nonempty. Then $b::w$ is nonempty as well, so its canonicality says its last bit is true. Since $w$ is nonempty, the last bit of $b::w$ is the last bit of $w$. Therefore the last bit of $w$ is true, proving that $w$ is canonical.
