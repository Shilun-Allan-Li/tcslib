<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/Bin.lean :: Complexity.LogProg.bits_injective -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Injectivity of Binary Expansion

**Claim.** Distinct natural numbers have distinct binary bit lists.

**Proof.** Suppose two natural numbers have the same binary bit list. Evaluating that list by `bitsVal` recovers the original number (`bitsVal_bits`), so applying this evaluation to the common list shows that the two numbers are equal. This proves injectivity.

**Key facts.** `Complexity.LogProg.bitsVal_bits`.
