<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/StrictFanOut.lean :: BoolCircuit.DAGCircuit.exists_isStrict_fanoutTwo -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Strict bounded fanout conversion

**Claim.** Every fanin two circuit on a positive number of inputs can be replaced by an equivalent circuit with strict gate arities, positive fanout at every nonoutput vertex, and fanout at most two, with size at most $20$ times the original size plus $60$.

**Proof.** First use the deconstancy construction to obtain a circuit whose gates are strict; this construction preserves the computed function and increases size by exactly $3$. The strict circuit conversion theorem then supplies an equivalent strict circuit with positive fanout at every nonoutput vertex, fanout at most two, and size at most $20$ times the deconstancy circuit's size. By evaluation preservation for deconstancy, the resulting circuit computes the original function. Its size is at most $20(C.size+3)=20C.size+60$.

**Key facts.** `BoolCircuit.DAGCircuit.deconst_strict`, `BoolCircuit.DAGCircuit.exists_isStrict_fanoutTwo_of_strict`, `BoolCircuit.DAGCircuit.deconst_eval`, `BoolCircuit.DAGCircuit.deconst_size`.
