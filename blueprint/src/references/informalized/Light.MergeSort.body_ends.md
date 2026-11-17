<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Lib/MergeSort.lean :: Light.MergeSort.body_ends -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Merge Sort Body Runtime

**Claim.** Under the stated procedure, memory, space, depth, and recursive-call hypotheses, the sorting body terminates within $\mathrm{sortTime}(|L|)$ and leaves memory satisfying the required sortedness and preservation properties.

**Proof.** 1. Split on whether the input length is at most one. In that case the body takes the skip branch, which terminates within the bound and leaves the input unchanged; `sorted_refl` supplies the required sortedness from the original segment representation.

2. Otherwise put $h=\lfloor(|L|+1)/2\rfloor$. The size inequalities ensure both recursive inputs are nonempty and shorter than $L$, and that each satisfies the recursive hypothesis's size condition. The halving procedure computes this $h$ without changing memory (`half_meets`). Apply the recursive hypothesis first to $L.take\ h$ at address $a$. Its sorted result is a permutation of that prefix, is nondecreasing, and preserves the required cells. Then apply the recursive hypothesis to $L.drop\ h$ at address $a+h$ in the resulting memory. The first recursive call's preservation property ensures that the second input segment remains represented; the second call's preservation property, in turn, ensures the first sorted segment remains represented.

3. The two sorted segments have lengths $h$ and $|L|-h$. The join procedure merges them and copies the result back, preserving the required outside cells (`join_ends`). The time split bound (`time_split`) shows that the two recursive costs together with halving and joining fit within $\mathrm{sortTime}(|L|)$. Finally, the permutation, order, and memory-preservation properties of the joined result give sortedness of the original list (`sorted_merge`).

**Key facts.** `Light.Ends.iteLast`, `Light.MergeSort.sorted_refl`, `Light.MergeSort.time_split`, `Light.half_meets`, `Light.Seg.take`, `Light.Seg.drop`, `Light.Seg.congr`, `Light.MergeSort.join_ends`, `Light.MergeSort.sorted_merge`, `Light.Ends.mono`.
