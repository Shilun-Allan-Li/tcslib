<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/CircuitSatReductionSpec.lean :: BoolCircuit.CktSatReduction.Emitter.emRun_n -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Advancing Through True Input Bits

**Claim.** Reading $k$ consecutive true bits from phase $n$ with vertex counter $z$ has the same output as starting in phase $n$ with counter $z+k$ on the remaining input.

**Proof.** Induct on $k$, generalizing $z$. At $k=0$ the inputs and states agree. For the successor case, the first true bit in phase $n$ keeps the machine in phase $n$ and increases the vertex counter by one. The remaining $k$ true bits are handled by the induction hypothesis, now starting at $z+1$. The resulting counter is $(z+1)+k=z+(k+1)$, as required.
