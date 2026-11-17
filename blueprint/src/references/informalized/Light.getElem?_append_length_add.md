<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Logic.lean :: Light.getElem?_append_length_add -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Indexing a program after concatenation

**Claim.** If $R$ has entry $b$ at index $i$, then $P_0++R$ has entry $b$ at index $|P_0|+i$.

**Proof.** The index $|P_0|+i$ lies in the $R$ portion of the concatenation, and subtracting the length of the initial block leaves index $i$. The list-indexing rule for a concatenation therefore identifies the requested entry with the given entry of $R$.
