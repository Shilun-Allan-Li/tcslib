<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clA5GroupAt_exact -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Selector as Ordered-List Lookup

**Claim.** The selector that chooses among the pinning groups, initial group, state groups, input groups, work groups ordered by time and tape, and acceptance groups equals lookup at index $i$ in that ordered list, with the empty formula as the out-of-range default.

**Proof.** The ordered list has consecutive blocks of lengths $n$, $1$, $T$, $T+1$, $k(T+1)$, and $T$. Lookup in a mapped range list returns the indexed family member when the index lies within that range and is absent otherwise. The work block has length $k(T+1)$ (`Complexity.clA5Work_get`), and its lookup at offset $j$ is the work group at time $j/k$ and tape $j\bmod k$. Now split the index through the listed blocks. If $i<n$, lookup returns the pinning group. Otherwise subtract $n$: offset zero is the initial group; after that, offsets below $T$ select state groups; the next $T+1$ select input groups. The next $k(T+1)$ offsets select work groups by the quotient-and-remainder formula. The remaining offsets select acceptance groups when below $T$, and otherwise lookup is absent, so its default is the empty formula. These are exactly the successive cases and subtractions defining the selector.

**Key facts.** `Complexity.clA5Work_get`.
