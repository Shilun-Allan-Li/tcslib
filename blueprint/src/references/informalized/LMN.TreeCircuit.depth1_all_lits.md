<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/CircuitTreeManip.lean :: LMN.TreeCircuit.depth1_all_lits -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Literals below a shallow gate

**Claim.** If a gate applied to a list of circuit trees has depth at most $1$, then every child in the list is a literal.

**Proof.** Take any child $c$ in the list. The shallow-gate depth bound implies that $c$ has depth $0$ (`TreeCircuit.depth1_children_are_lits`). A depth-zero circuit is a literal (`TreeCircuit.depth0_is_lit`), so there is a literal equal to $c$.

**Key facts.** `LMN.TreeCircuit.depth1_children_are_lits`, `LMN.TreeCircuit.depth0_is_lit`.
