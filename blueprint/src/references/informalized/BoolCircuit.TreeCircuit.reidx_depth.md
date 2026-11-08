<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/CircuitReindex.lean :: BoolCircuit.TreeCircuit.reidx_depth -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Depth Under Reindexing

**Claim.** Reindexing the inputs of a Boolean circuit preserves its depth.

**Proof.** Proceed by structural induction on the circuit. A literal has depth zero, and reindexing it leaves it a literal, so its depth is unchanged. For a gate with children $cs$, reindexing maps each child individually and preserves the gate type. The depth is one plus the maximum child depth, with the empty list contributing zero. By the induction hypotheses, every mapped child has the same depth as its original; thus the two lists have the same maximum depth, and the gate depths agree. The induction hypothesis applies to each child because each belongs to the gate's child list.

**Key facts.** `BoolCircuit.TreeCircuit.ind`.
