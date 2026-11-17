<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Sweep.lean :: Turing.FinTM.indexedFold -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Indexed Transduction of a Duplicate-Free List

**Claim.** Sweeping through the indexed cells listed by a duplicate-free list updates the table at each listed index using that index's local rule and original table value, leaves all other entries unchanged, and outputs the listed indices paired with their corresponding local-rule outputs.

**Proof.** Induct on the list of indices, generalizing over the initial table. For the empty list, the sweep leaves the table unchanged and produces no output. For a list beginning with $i$, duplicate-freeness says that $i$ does not occur in the tail. The first sweep step applies the local rule at $i$, updating only the table entry there and recording its second component. Apply the induction hypothesis to the tail starting from this updated table. At index $i$, the final table has the value assigned by the first update. At any other index $j$, the first update leaves the entry unchanged; if $j$ occurs in the tail, the induction hypothesis assigns the tail's local-rule value. Since $i$ is absent from the tail, that value is computed from the original entry $s(j)$, not from a previously changed one. If $j$ is absent from the whole list, it remains unchanged. The recorded outputs are the first output followed by the tail outputs; the tail's local-rule outputs agree with those computed from the original table for the same no-repetition reason.
