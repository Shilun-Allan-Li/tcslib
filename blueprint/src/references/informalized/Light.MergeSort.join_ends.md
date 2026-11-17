<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Lib/MergeSort.lean :: Light.MergeSort.join_ends -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Merge Sort Join Postcondition

**Claim.** Under the stated procedure, bounds, segment representations, and depth condition, the join procedure terminates within cost $56n+34$ and leaves the merged list stored at $a$, with the required preservation properties.

**Proof.** The two input lists have lengths $h$ and $n-h$, so their merge has length $n$. Apply the merge procedure to the lists stored at $a$ and $a+h$, writing into the free interval beginning at $fr$. The hypotheses give the required space bounds and separation, so `merge_meets` yields a memory that preserves the original memory outside that free interval and stores the merge there. Next apply the copy procedure from $fr$ back to $a$. The source and destination intervals fit in space and are disjoint because $a+n\le fr$; `copy_meets` shows that the destination now contains the merged list and that memory outside the destination interval is preserved relative to the post-merge memory. Combining the merge's preservation outside the free interval with the copy's preservation outside the destination interval gives the stated memory witness. The copied segment representation follows by composing the copy's cellwise equality with the merge's segment representation.

**Key facts.** `Light.merge_meets`, `Light.copy_meets`.
