<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Lib/MergeSort.lean :: Light.sort_meets -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Merge sort correctness and resource bound

**Claim.** Under the stated program, word-limit, memory-interval, and recursion-depth hypotheses, the sort procedure runs within the stated bound and returns a sorted permutation of the input interval while preserving the required memory outside that interval.

**Proof.** Proceed by strong induction on the list length, allowing the starting address, list, and memory function to vary. At length $n$, the body-correctness theorem (`MergeSort.body_ends`) reduces the sort to its recursive calls on the two halves, along with the half, merge, and copy procedures. Its induction hypothesis is applicable to each recursive sublist: the split provides the required interval and segment conditions, and each sublist is shorter. The main depth calculation uses the ceiling-log identity $\lceil\log_2 n\rceil=\lceil\log_2\lceil n/2\rceil\rceil+1$ for the nontrivial split, together with monotonicity of the ceiling logarithm and the bound on the recursive sublist length. These facts show that the available depth suffices for the recursive call at depth $d+1$. The body theorem therefore gives the required execution and sorted-permutation postcondition with the stated time bound; converting this body execution into the procedure-level result uses `Meets.of_body` and the program’s specified sort body.

**Key facts.** `Light.Meets.of_body`, `Light.MergeSort.body_ends`.
