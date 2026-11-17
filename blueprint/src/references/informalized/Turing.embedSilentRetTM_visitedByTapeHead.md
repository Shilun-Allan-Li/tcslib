<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Embed.lean :: Turing.embedSilentRetTM_visitedByTapeHead -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Visited heads under return embedding

**Claim.** For every time bound $t$ and tape index $j$, the return machine and the silent embedding visit the same set of head positions on tape $j$ through time $t$.

**Proof.** The return machine's transition on left-summand states is the return-action form of the silent machine's transition, and its right-summand state idles. The visited-position invariance theorem (`Turing.embedReturn_visited`) says that for machines with these two transition properties, mapping the initial state into the left summand preserves the set of head positions visited at every time bound. The silent return machine has precisely these transition properties, yielding the asserted equality.

**Key facts.** `Turing.embedReturn_visited`.
