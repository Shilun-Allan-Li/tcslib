<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerVerifier.lean :: Complexity.Meyer.evalAtom_congr -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Congruence of atomic evaluations

**Claim.** If the six decoded components of two Boolean words agree componentwise, then every atom over the states and work tapes of the machine has the same Boolean evaluation on both words.

**Proof.** First, the two words have the same auxiliary index encoding: its definition uses only the decoded index and final components, which agree by hypothesis. For an answer atom, split into the four time-word types and six auxiliary-word types. In each case, the produced time word agrees on the two inputs: it is either the decoded time word, its fixed-width increment, or a constant word whose length depends only on the input component. The same reasoning applies to the auxiliary word, using also the equality of the index encoding in the index-based cases. Thus the arguments supplied to the answer predicate agree, including the description and input words, so its Boolean value agrees. For each remaining atom, unfolding its definition shows that it tests lengths, inequalities, or equality of expressions built from the decoded components and the auxiliary index encoding. Those expressions agree, so the test has the same value.
