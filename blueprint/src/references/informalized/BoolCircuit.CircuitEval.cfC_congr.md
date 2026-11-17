<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/CircuitEvalRun.lean :: BoolCircuit.CircuitEval.cfC_congr -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Copy configurations ignore bound witnesses

**Claim.** For fixed $z,i_0,n,x$, the copy configurations defined using bounds for $i_0+h\le |z|$ and $i_0+h'\le |z|$ are equal whenever $h=h'$.

**Proof.** Substitute the equality $h=h'$. The two configurations then have the same input position, value tape, mark tape, head position, and output; the bound witnesses affect only the proof that the input position is valid, not the configuration itself. Thus the configurations are definitionally equal.
