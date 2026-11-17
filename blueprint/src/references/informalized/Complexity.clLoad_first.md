<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clLoad_first -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First Completion of a Row Load

**Claim.** When the row has at least one field, the loader reaches the complete-row configuration for the first time at a positive time bounded by $l(2U+3W+7)$, under the given bounds on old and new field lengths.

**Proof.** The complete-run lemma (`clLoad_complete`) supplies a time $B$ within the stated bound at which the loader is in the complete-row configuration. The initial configuration is not already in that state: its field index is zero, whereas the final index is $l>0$. The completed loader state is fixed by one step (`clLoad_idle`). Apply the first-visit lemma (`clFirst`) to this run, using that initial-state inequality and the fixed-state property. It produces a positive time $t\le B$ at which the same final configuration is reached, with no earlier visit to the complete-row control. The bound on $B$ gives the required bound on $t$.

**Key facts.** `Complexity.clLoad_complete`, `Complexity.clLoad_idle`, `Complexity.clFirst`.
