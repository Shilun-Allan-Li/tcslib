<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathHardDecide.lean :: Complexity.PathHard.not_mem_indexLang_of_pairDecode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Undecodable strings are not indexed

**Claim.** If the aligned pair parser fails on a bit string $y$, then $y$ does not belong to the indexed language for any predicate on bit strings and nonnegative integers.

**Proof.** If $y$ belonged to the indexed language, it would equal a pair encoding of some bit string $x$ and the binary expansion of some integer $i$. The parser recovers both components of every pair encoding (`pairDecode_pairEncode`), so parsing $y$ would return a pair rather than fail. This contradicts the hypothesis that the parser returns none.

**Key facts.** `Turing.pairDecode_pairEncode`.
