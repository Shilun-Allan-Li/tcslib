<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Lib/MergeSort.lean :: Light.MergeSort.sorted_refl -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reflexive Sortedness for Short Lists

**Claim.** If $L$ has length at most one and is stored at $a$ in memory $\mu$, then it is sorted there relative to $\mu$.

**Proof.** Take $L$ itself as the witnessing list. It is stored at $a$ by hypothesis and is a permutation of itself. A list of length at most one is either empty or a singleton; both are nondecreasing. Finally, the required memory preservation holds because the initial and final memories are both $\mu$.
