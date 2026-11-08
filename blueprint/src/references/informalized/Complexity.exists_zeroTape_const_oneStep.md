<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ZeroSpace.lean :: Complexity.exists_zeroTape_const_oneStep -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Constant output in one step without work tapes

**Claim.** There is a finite binary Turing machine with zero work tapes that halts within one step and outputs the single bit 1 on every binary input.

**Proof.** Take the machine `constTrueTM`. Its work-tape count is zero by its definition, and `constTrueTM_computesInTime` supplies, for every input, a computation producing [true] within one step. Together these establish the claim.

**Key facts.** `Complexity.constTrueTM_computesInTime`.
