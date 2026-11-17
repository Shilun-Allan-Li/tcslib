<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/CircuitSatReductionValid.lean :: BoolCircuit.CktSatReduction.T_nil -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Transduction of the Empty String

**Claim.** For every transducer state $q$, processing the empty bit string from $q$ returns the empty bit string.

**Proof.** By the definition of transduction, processing an empty input consumes no bits and emits no output. Hence $T(q,[])=[].$
