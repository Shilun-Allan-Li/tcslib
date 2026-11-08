<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/TreeNCAC.lean :: BoolCircuit.TreeNCLevel_subset_ACLevel -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Tree circuit class inclusion

**Claim.** For every natural number $i$, the class of languages recognized by polynomial-size tree-circuit families of polylogarithmic depth exponent $i$ and fan-in at most two is contained in the class recognized by polynomial-size tree-circuit families of polylogarithmic depth exponent $i$.

**Proof.** Take any language in the first class. Its witness is a tree-circuit family with polynomial size, the stated depth bound, and fan-in at most two. The theorem that every such witness for the first class is also a witness for the second class preserves the polynomial-size and depth conditions and forgets the additional fan-in restriction. Therefore the language belongs to the second class.

**Key facts.** `Language.InTreeNC.inTreeAC`.
