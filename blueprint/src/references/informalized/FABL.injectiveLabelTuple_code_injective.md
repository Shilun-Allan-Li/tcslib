<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.injectiveLabelTuple_code_injective -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Injectivity of the Tuple Code

**Claim.** The encoding of an injective tuple by its image and the corresponding bijection is injective: equal codes determine equal tuples.

**Proof.** Suppose two injective tuples have equal codes. The second component of each code is a bijection from the tuple positions to the elements of its image. Evaluating the equality of codes at any position $i$ shows that these bijections have the same value there. Taking the underlying element of that value gives equality of the two tuples at $i$. Since this holds for every position, the tuples are equal.
