<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Logic.lean :: Light.getElem?_append_of_eq_some -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Indexed entries under concatenation

**Claim.** If the entry at index $p$ of $P$ is $b$, then the entry at index $p$ of $P$ concatenated with $R$ is still $b$.

**Proof.** The hypothesis that the indexed lookup in $P$ equals $b$ implies that $p$ is within the length of $P$. At any such index, looking up an entry in a concatenation gives the same result as looking it up in the first list. Thus the lookup in $P\mathbin{++}R$ is $b$.
