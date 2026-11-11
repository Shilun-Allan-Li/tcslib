<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Compat.lean :: List.Pairwise.merge -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Merge preserves order

**Claim.** If two lists in a linearly ordered type are nondecreasing, their merge is nondecreasing.

**Proof.** View the order relation as a Boolean-valued comparison. The merge theorem for sorted lists says that merging two lists sorted by a transitive comparison preserves sortedness, provided the comparison is total. Here transitivity is the transitivity of $\le$ (that is, $\le$), and totality is linearity of the order. The hypotheses that each input list is nondecreasing give the required sortedness, so the merged list is nondecreasing.

**Caveat.** The proof relies on the imported sorted-merge theorem, which is not listed in upstream; the account states its mathematical content.
