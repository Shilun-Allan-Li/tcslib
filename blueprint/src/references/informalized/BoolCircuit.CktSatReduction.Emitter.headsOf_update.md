<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/CircuitSatReductionMachine.lean :: BoolCircuit.CktSatReduction.Emitter.headsOf_update -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating work-tape head positions

**Claim.** Replacing the integer-valued head position at index $t$ by $m$ agrees with first replacing the natural-valued component at $t$ by $m$ and then converting the function to integers.

**Proof.** To show the two functions agree, evaluate them at an arbitrary index $i$. If $i=t$, both values are the integer cast of $m$. If $i\ne t$, neither update changes that component, so both values are the integer cast of $v(i)$.
