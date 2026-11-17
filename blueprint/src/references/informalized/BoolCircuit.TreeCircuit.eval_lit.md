<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Basic.lean :: BoolCircuit.TreeCircuit.eval_lit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of a Literal Circuit

**Claim.** A circuit consisting of the single leaf $l$ evaluates on any assignment $x$ to the value of the literal $l$ under $x$.

**Proof.** By the definition of circuit evaluation, a literal leaf evaluates directly to the evaluation of its label. Therefore the circuit consisting of the leaf $l$ evaluates to $l$'s value under $x$.
