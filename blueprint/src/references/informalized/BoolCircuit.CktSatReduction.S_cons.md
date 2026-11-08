<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/CircuitSatReductionValid.lean :: BoolCircuit.CktSatReduction.S_cons -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Output on a leading bit

**Claim.** For the specified transducer, processing a bit $b$ followed by a finite bit string $r$ from state $q$ outputs $[b]$ if $q=o$ (and nothing otherwise), followed by the output on $r$ from the state reached after reading $b$.

**Proof.** By the recursive definition of the transducer, its output on a nonempty input is the output produced while reading the first bit, concatenated with the output on the remaining string from the resulting state. Here that first-bit output is the one-bit list $[b]$ exactly when the current state is $o$, and is empty in every other state. Substituting this output rule and the transition function gives the stated formula.
