<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/CircuitEvalRun.lean :: BoolCircuit.CircuitEval.cfS_congr -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Scanning configurations ignore bound witnesses

**Claim.** For fixed $z,\phi,r$, the scanning configurations defined using bounds for $i\le |z|$ and $i'\le |z|$ are equal whenever $i=i'$.

**Proof.** Substitute $i=i'$. The two configurations now have identical state, input position, work tapes, head positions, and output. The bound witnesses certify validity of the input positions but do not change those positions, so the configurations are equal by their definitions.
