<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clRecords_native -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-time trajectory output

**Claim.** For the specified polynomially bounded input length and quadratic horizon, the function returning the serialized trajectory prefix is polynomial-time computable.

**Proof.** Use the polynomial-time construction of the packed recording input (`Complexity.clRecordArgument_native`) as the input map, and use the recording output machine with the quadratic running-time bound supplied by `Complexity.clRecordOutput_quadratic`. The exact header-layout identity (`Complexity.clHeaderLayout_exact`) shows that the packed input produced by the input map has precisely the recorder's required initial words: the simulated input, the relevant numerical parameters in binary, and the recorder's other initialized tapes. Applying the polynomial-time image principle (`Complexity.clNative_image`) to this input map and output machine proves that their composition computes the trajectory prefix in polynomial time.

**Key facts.** `Complexity.clRecordArgument_native`, `Complexity.clHeaderLayout_exact`, `Complexity.clRecordOutput_quadratic`, `Complexity.clNative_image`.
