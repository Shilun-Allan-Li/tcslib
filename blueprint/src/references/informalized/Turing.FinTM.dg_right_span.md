<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean :: Turing.FinTM.dg_right_span -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rightward Growth Span

**Claim.** Starting in right-growth phase at counter zero, the simulator reaches counter $k$ in $k$ steps, with its work head always between $z$ and $z+k$. It leaves the input-head position and output unchanged, adds the reversed encoded right guard block to the left list, and drops the first $k$ entries of the right list.

**Proof.** Let $w$ be the encoded right guard block; it has length $k$. The simulator's transition at each counter $i<k$ writes the $i$th symbol of $w$, advances the head right, and increments the counter. The general rightward-generation span lemma (`dgSpan_generate_right`) therefore applies with this list and these counter states. It gives the endpoint after $k$ steps, places the consumed prefix in reverse order on the left, drops that prefix from the right, and bounds every intermediate head position between $z$ and $z+k$. Since the prefix has the full length of $w$, it is all of $w$, yielding the stated stacks and endpoint.

**Key facts.** `Turing.FinTM.dgSpan_generate_right`.
