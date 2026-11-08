<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Lib/MergeSort.lean :: Light.MergeSort.sorted_merge -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sortedness of a Merge

**Claim.** If each input list is a nondecreasing permutation of the corresponding prefix or suffix of $L$, and the stated memory-preservation and segment conditions hold, then the merged list witnesses sortedness of $L$ relative to the original memory.

**Proof.** Use $S_1\mathbin{.merge}S_2$ as the list witnessing sortedness. The merge is a permutation of $S_1++S_2$ (`List.merge_perm_append`); since permutations are preserved by appending, this concatenation is a permutation of $(L.take\ h)++(L.drop\ h)$, which equals $L$ (`List.take_append_drop`). The merge is nondecreasing because both input lists are nondecreasing (`List.Pairwise.merge`), and the assumed segment condition says that this merged list is stored at $a$ in $\mu_4$. It remains to check preservation below $fr$ outside the interval for $L$. At any such cell, the final change from $\mu_3$ to $\mu_4$ preserves its value by the destination-interval condition. The merge's temporary interval beginning at $fr$ is disjoint from cells below $fr$, so $\mu_2$ and $\mu_3$ agree there. The two recursive preservation conditions then transfer equality successively from $\mu_2$ to $\mu_1$ and from $\mu_1$ to $\mu$. The prefix and suffix lengths are $h$ and $|L|-h$, respectively, so the required outside conditions apply.

**Key facts.** `List.Pairwise.merge`.
