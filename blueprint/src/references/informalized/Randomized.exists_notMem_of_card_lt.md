<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/SipserGacs.lean :: Randomized.exists_notMem_of_card_lt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# An Element Outside a Proper Subset

**Claim.** If a finite subset $S$ of a finite type has smaller cardinality than the whole type, then some element of the type lies outside $S$.

**Proof.** If there were no element outside $S$, then every element of the type would belong to $S$, so $S$ would be the whole type. Their cardinalities would then be equal, contradicting the assumed strict inequality.
