<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/CircuitSatReductionValid.lean :: BoolCircuit.CktSatReduction.S_ones -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Ignoring repeated ones

**Claim.** If reading a one leaves the state $q$ unchanged and $q\ne o$, then reading any number of consecutive ones followed by $r$ from $q$ produces the same output as reading $r$ from $q$.

**Proof.** Induct on the number $k$ of leading ones. When $k=0$, the inputs coincide. For the induction step, split off the first one. Since $q\ne o$, the transducer emits nothing on that bit; since reading one leaves the state unchanged, the remaining input is processed from $q$. The one-bit output formula (`S_cons`) thus reduces the output to that on the remaining $k$ ones followed by $r$, which equals the output on $r$ by induction.

**Key facts.** `BoolCircuit.CktSatReduction.S_cons`.
