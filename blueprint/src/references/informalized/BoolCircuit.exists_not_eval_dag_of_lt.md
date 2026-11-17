<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/DAGHardFunctions.lean :: BoolCircuit.exists_not_eval_dag_of_lt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Hard functions from a circuit count

**Claim.** If $(S+1)(3(S+1)^2)^S S<2^{2^n}$, then some Boolean function on $n$ input bits disagrees with every well-formed fan-in-two acyclic circuit of size at most $S$ on at least one input.

**Proof.** Let $T$ be the set of Boolean functions computed by well-formed fan-in-two acyclic circuits of size at most $S$. The circuit-count bound (`card_computable_dag_le`) gives $|T|\le(S+1)(3(S+1)^2)^S S$. Meanwhile there are exactly $2^{2^n}$ Boolean functions on $n$ bits: there are $2^n$ possible inputs and each function independently chooses a Boolean output for each. The strict hypothesis makes $T$ smaller than the full function space, so choose a function $f$ outside $T$. If some eligible circuit agreed with $f$ on every input, its computed function would equal $f$, placing $f$ in $T$, a contradiction. Thus every eligible circuit disagrees with $f$ somewhere.

**Key facts.** `BoolCircuit.card_computable_dag_le`.
