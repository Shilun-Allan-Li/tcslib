<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathHardRegs.lean :: Complexity.PathHard.orc_bit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First Oracle Component

**Claim.** For every finite nondeterministic Turing machine $N$, bit string $y$, and natural number $p$, the first oracle component on the pairing of $y$ with the binary representation of $p$ returns the bit of $y$ at position $p$, using false when that position is out of range.

**Proof.** The first oracle component is the indicator of the input-bit language. The pairing characterization of that language shows that its value on this encoded query is the decision of whether $y.getD\ p\ false=true$ (Complexity.indicator_indexLang_pairEncode). If the defaulted bit is true, this decision is true; if it is false, the decision is false. In either case the result is exactly the defaulted bit.

**Key facts.** `Complexity.indicator_indexLang_pairEncode`.
