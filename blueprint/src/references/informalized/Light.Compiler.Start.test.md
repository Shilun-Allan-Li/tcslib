<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/Simulation.lean :: Light.Compiler.Start.test -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Compiled conditions decide their truth

**Claim.** A compiled condition executes within its size bound and branches to the fall-through position when it holds, or to the specified target when it does not, while changing memory only at scratch locations.

**Proof.** Apply the compilation correctness theorem for conditions (\texttt{Light.Compiler.decides_compileCond}) to the framed start configuration, its bounded light state, and the given compiled-code placement, width bound, and safety hypothesis. That theorem supplies a resulting memory and a step count bounded by the condition's size; it also gives agreement with the original memory outside the scratch locations and the two execution conclusions according to whether the condition holds. These are precisely the required properties.

**Key facts.** `Light.Compiler.decides_compileCond`.
