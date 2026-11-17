<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Util/List.lean :: List.length_flatMap_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length bound for a flattened list

**Claim.** If every list assigned to an element of $l$ has length at most $c$, then concatenating those lists has length at most $\text{length}(l)c$.

**Proof.** The length of the concatenation is the sum, over the entries of $l$, of the lengths of their assigned lists. Each such length is at most $c$, so the sum is at most the sum of one copy of $c$ for each entry of $l$. There are $\text{length}(l)$ entries, making this upper bound $\text{length}(l)c$.
