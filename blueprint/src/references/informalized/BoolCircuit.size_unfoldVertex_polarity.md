<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/FormulaFanOut.lean :: BoolCircuit.size_unfoldVertex_polarity -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polarity independence of unfolded size

**Claim.** For every fuel bound and vertex, unfolding with either Boolean polarity gives circuits of equal size.

**Proof.** Proceed by induction on the fuel. At fuel zero, both unfoldings are the same empty node, so their sizes agree. At successor fuel, split according to whether the vertex is an input. If it is, the two results are literals; their signs may differ, but every literal has size one. Otherwise the vertex is unfolded through its gate. The induction hypothesis says that each recursive unfolding of an argument has size independent of polarity. The gate-level fact that unfolding preserves this independence, regardless of whether the gate is AND, OR, or NOT (`size_unfoldGate_polarity`), then gives equality of the two resulting sizes.

**Key facts.** `BoolCircuit.size_unfoldGate_polarity`.
