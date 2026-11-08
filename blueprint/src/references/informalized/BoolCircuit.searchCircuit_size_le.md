<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/KarpLiptonSearch.lean :: BoolCircuit.searchCircuit_size_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Size bound for the search circuit

**Claim.** If each of the first $m$ circuits has size at most $S$, then the search circuit after $m$ stages has size at most $n+1+m(S+1)$.

**Proof.** The bound on the number of gates in the search state (`length_searchState_le`), applied at stage $m$, gives at most $1+m(S+1)$ gates. The search circuit has this state’s gate list and has size equal to the number of input vertices $n$ plus its number of gates. Substitution yields the claimed bound.

**Key facts.** `BoolCircuit.length_searchState_le`.
