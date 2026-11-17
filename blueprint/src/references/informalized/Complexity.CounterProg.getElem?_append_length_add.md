<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CounterProgInput.lean :: Complexity.CounterProg.getElem?_append_length_add -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Indexing a concatenated list

**Claim.** For bit lists $\mathrm{pre}$ and $\mathrm{suffix}$ and any $p\in\mathbb N$, the element at index $|\mathrm{pre}|+p$ of their concatenation, if present, equals the element at index $p$ of $\mathrm{suffix}$, if present.

**Proof.** The index $|\mathrm{pre}|+p$ is at or beyond the boundary between the two lists. The list-indexing rule for concatenation therefore reduces the lookup to index $(|\mathrm{pre}|+p)-|\mathrm{pre}|=p$ in the suffix. This rule preserves the optional result, so it also covers the case where that index is out of range.
