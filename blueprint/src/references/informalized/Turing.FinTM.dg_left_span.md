<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean :: Turing.FinTM.dg_left_span -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Left-growth sweep span

**Claim.** An indexed left-growth sweep takes $k$ steps, moves the frontier from $z$ to $z-k$, prepends the row determined by the head flags to the left stack, drops the first $k$ entries of the right stack, and keeps the head within $[z-k,z]$.

**Proof.** Read the row to be generated from right to left: the $i$th visited cell corresponds to tape index $k-1-i$, has no tape symbol, carries that tape's specified head flag, and has its preceding-block flag cleared. For each counter value below $k$, the simulator's transition moves left, writes this cell, and increments the counter; this is precisely the transition condition required by the left-generation span lemma (`dgSpan_generate_left`). Applying that lemma for all $k$ cells yields the counter-$k$ state and frontier $z-k$. The generated cells are placed before the old left stack in the lemma's order, which, after reversing the right-to-left generation list, is exactly the encoded row prepended to $l$. The first $k$ entries of the right stack are removed, and the span lemma bounds all intermediate positions by $z-k$ and $z$.

**Key facts.** `Turing.FinTM.dgSpan_generate_left`.
