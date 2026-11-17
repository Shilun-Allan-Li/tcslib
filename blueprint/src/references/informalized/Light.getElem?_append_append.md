<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Logic.lean :: Light.getElem?_append_append -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Indexing a concatenated program

**Claim.** If $B$ has entry $b$ at index $i$, then the concatenation $P_0++B++R$ has entry $b$ at index $|P_0|+i$.

**Proof.** At index $|P_0|+i$, the concatenation has moved past the initial block $P_0$ and the remaining index is $i$. The list-indexing rule for concatenation reduces the lookup to index $i$ in $B++R$. Since that lookup in $B$ is already known to be $b$, adjoining $R$ does not change it (`Light.getElem?_append_of_eq_some`).

**Key facts.** `Light.getElem?_append_of_eq_some`.
