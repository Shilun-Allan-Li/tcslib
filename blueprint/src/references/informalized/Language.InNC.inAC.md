<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/NCAC.lean :: Language.InNC.inAC -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# NC Circuits Give AC Circuits

**Claim.** Every language recognized by a well-formed fan-in-two circuit family with polynomial size and the stated polylogarithmic depth bound is recognized by a well-formed circuit family with the same size and depth bounds.

**Proof.** Take a family witnessing the NC hypothesis. Its fan-in-two property includes well-formedness (`BoolCircuit.DAGCircuitFamily.HasFaninTwo.isWellFormed`). The family already has the required polynomial size, depth bound, and recognized language. Thus the same family witnesses the AC claim.

**Key facts.** `BoolCircuit.DAGCircuitFamily.HasFaninTwo.isWellFormed`.
