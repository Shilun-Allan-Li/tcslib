<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/Program.lean :: Complexity.LogProg.length_argSegs -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length of Argument Segmentation

**Claim.** For every finite list of Boolean words, its argument segmentation has the same length as the original list.

**Proof.** Induct on the list. The empty list segments to the empty list, and a one-word list segments to a one-element list, so the claim holds in those cases. For a list with at least two words, the segmentation places the first word in one segment and recursively segments the remaining list. The induction hypothesis gives the length of that recursive segmentation; adding the first segment gives the original list's length.
