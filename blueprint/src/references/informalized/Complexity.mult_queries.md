<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/Mult.lean :: Complexity.mult_queries -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bit and length oracle queries

**Claim.** The first oracle returns the queried bit of a finite bit string, defaulting to false out of range, and the second returns whether the queried index is less than the string’s length.

**Proof.** For each oracle, the encoded query is exactly a pair consisting of the given string and the binary representation of the index. The pair-encoding indicator theorem says that the indicator of an indexed language on such an encoding returns the truth value of that language’s defining predicate (`indicator_indexLang_pairEncode`). For the bit language, that predicate says the string’s defaulted bit at the index is true; for the length language, it says the index is below the string’s length. Unfolding these two predicates gives the stated Boolean answers.

**Key facts.** `Complexity.indicator_indexLang_pairEncode`.
