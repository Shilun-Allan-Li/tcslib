<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/CircuitSat.lean :: BoolCircuit.TreeCircuit.toCNF_length_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Clause count bound

**Claim.** For every Boolean circuit $C$ on $n$ variables, the length of its conjunctive normal form translation is at most three times the size of $C$.

**Proof.** The translation places one additional clause in front of the Tseitin translation, so its length is one plus the length of the Tseitin translation. The Tseitin length bound gives a strict inequality with $3\,\mathrm{size}(C)$; since lengths and sizes are integers, this implies that the translated CNF length is at most $3\,\mathrm{size}(C)$.

**Key facts.** `BoolCircuit.TreeCircuit.tseitin_length_lt`.
