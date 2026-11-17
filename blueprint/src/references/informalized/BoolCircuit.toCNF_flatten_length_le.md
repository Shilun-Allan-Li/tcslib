<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Encoding.lean :: BoolCircuit.toCNF_flatten_length_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Flattened CNF Length Bound

**Claim.** For every Boolean circuit tree $C$, the flattened list of clauses in its conjunctive normal form has length at most $7\,\mathrm{size}(C)$.

**Proof.** The conjunctive normal form adds a root clause to the Tseitin encoding, so its flattened length is the flattened Tseitin length plus the contribution of that clause. The Tseitin bound gives $\mathrm{length}(C.\mathrm{tseitin.flatten})+3\le 7\,\mathrm{size}(C)$. Comparing the two lengths and using this stronger additive margin yields the claimed bound.

**Key facts.** `BoolCircuit.tseitin_flatten_length_le`.
