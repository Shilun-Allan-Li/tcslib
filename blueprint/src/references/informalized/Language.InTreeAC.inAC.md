<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/NCAC.lean :: Language.InTreeAC.inAC -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Tree circuits lie in circuit classes

**Claim.** A language recognized by polynomial-size Boolean circuit trees of the specified polylogarithmic depth is recognized by a well-formed directed acyclic circuit family with polynomial size and the same depth bound form.

**Proof.** Choose a tree-circuit family witnessing the hypothesis and replace every tree by its associated directed acyclic circuit. Each resulting circuit is well formed (`BoolCircuit.TreeCircuit.toDAG_isWellFormed`). The conversion preserves polynomial size (`BoolCircuit.TreeCircuitFamily.isPolySize_toDAG`) and the stated polylogarithmic depth bound (`BoolCircuit.TreeCircuitFamily.hasPolylogDepth_toDAG`). It also preserves the recognized language (`BoolCircuit.TreeCircuitFamily.language_toDAG`), so the converted family witnesses membership in the circuit class.

**Key facts.** `BoolCircuit.TreeCircuit.toDAG_isWellFormed`, `BoolCircuit.TreeCircuitFamily.isPolySize_toDAG`, `BoolCircuit.TreeCircuitFamily.hasPolylogDepth_toDAG`, `BoolCircuit.TreeCircuitFamily.language_toDAG`.
