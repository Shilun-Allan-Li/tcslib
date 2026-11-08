<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyGadget.lean :: BoolCircuit.runWith_embedGates_getD -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of an embedded circuit

**Claim.** Executing the embedded gates of a circuit from an initial list produces, at the designated output position, the circuit’s value on the input read from the specified source indices.

**Proof.** Let the embedded index map send each input vertex to its specified source index and each gate vertex to the corresponding position in the enlarged list. The source hypotheses ensure that input vertices map within the initial list; the circuit’s acyclicity condition and the bound for the embedding map (`embedMap_lt`) ensure that gate arguments map to already available positions. The execution correspondence lemma (`runWith_remap_rel`), applied to the relation of equality, then identifies each remapped gate’s evaluation with the original gate’s evaluation on the circuit’s input. In particular, at the circuit output vertex, the remapped execution has the same value as the original circuit. Repeated arguments can be removed without changing any gate’s value (`runWith_eval_map_dedupArgs`), so the embedded gate list has the same execution as the remapped list. Now split off the final output gate using the execution rule for appended lists (`runWith_append`). The remapped gates have added exactly one value per circuit gate, hence the final output gate reads the remapped output vertex at the designated position. That gate is an AND gate with a single argument, so its output is precisely that vertex’s value, as required.

**Key facts.** `BoolCircuit.DAGGate.eval_remap`, `BoolCircuit.embedMap_lt`, `BoolCircuit.runWith_remap_rel`, `BoolCircuit.runWith_eval_map_dedupArgs`, `BoolCircuit.runWith_append`, `BoolCircuit.runWith_singleton`.
