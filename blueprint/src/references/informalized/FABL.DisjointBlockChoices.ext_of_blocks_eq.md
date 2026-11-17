<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.DisjointBlockChoices.ext_of_blocks_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniqueness of Block Choices

**Claim.** Two choices of successive pairwise disjoint blocks are equal if their ordered lists of blocks are equal.

**Proof.** Proceed by induction on the number of blocks, allowing the remaining set to vary. With zero blocks, both choices are elements of the one-element type, so they are equal. For the successor case, write each choice as its first block followed by the remaining choice. Equality of the block lists gives equality of the first blocks and equality of the tails. The first-block equality is equality of the underlying finsets, hence equality of the corresponding subtype elements; applying the induction hypothesis to the tails then gives equality of the full choices.
