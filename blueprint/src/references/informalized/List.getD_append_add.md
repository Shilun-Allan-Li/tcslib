<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Util/List.lean :: List.getD_append_add -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lookup After Concatenation

**Claim.** In the concatenation $l++l'$, lookup at position $\operatorname{length}(l)+j$ with default $d$ equals lookup at position $j$ in $l'$ with the same default.

**Proof.** The lookup in a concatenation, once the index is at least the length of the first list, is lookup in the second list at the index reduced by that length. Here the index is $\operatorname{length}(l)+j$, so subtracting $\operatorname{length}(l)$ leaves $j$.
