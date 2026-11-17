<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/NCAC.lean :: Language.InTreeNC.inNC -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Tree circuits as DAG circuits

**Claim.** Any language recognized by polynomial-size, fan-in-two circuit trees of the stated polylogarithmic depth is recognized by well-formed acyclic fan-in-two circuits of polynomial size and the same depth bound.

**Proof.** Choose a tree family witnessing the hypothesis. Convert each tree to its associated directed acyclic circuit, preserving the input length. For each input length, the conversion theorem gives a well-formed circuit whose gates have fan-in at most two. The family conversion preserves polynomial size and the polylogarithmic depth bound. Finally, the converted circuit and the original tree have the same evaluation on every input, so their recognized languages agree; thus this family witnesses the conclusion.

**Key facts.** `BoolCircuit.TreeCircuit.toDAG_isFaninTwo`, `BoolCircuit.TreeCircuitFamily.isPolySize_toDAG`, `BoolCircuit.TreeCircuitFamily.hasPolylogDepth_toDAG`, `BoolCircuit.TreeCircuitFamily.language_toDAG`.
