<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/VWord.lean :: Complexity.getD_drop -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Indexing after dropping a prefix

**Claim.** For a Boolean list $y$ and natural numbers $a,i$, the element at index $i$ of the list obtained by dropping its first $a$ entries, with false as the out-of-range default, equals the element at index $a+i$ of $y$ with the same default.

**Proof.** This is the general list indexing identity that dropping a prefix of length $a$ shifts every subsequent index by $a$ (`List.getD_drop`). Apply it with the default value false.

**Key facts.** `List.getD_drop`.
