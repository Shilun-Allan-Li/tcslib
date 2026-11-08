<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathHardRegs.lean :: Complexity.PathHard.orc_len -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input-Length Oracle Component

**Claim.** For every finite nondeterministic Turing machine $N$, bit string $y$, and natural number $p$, the second oracle component on the pairing of $y$ with the binary representation of $p$ returns true exactly when $p<|y|$.

**Proof.** The second component is the indicator of the input-length language. The pairing characterization of this language identifies the oracle value with the decision of the predicate $p<|y|$ (Complexity.indicator_indexLang_pairEncode). Hence it is true exactly when the index is less than the length of $y$.

**Key facts.** `Complexity.indicator_indexLang_pairEncode`.
