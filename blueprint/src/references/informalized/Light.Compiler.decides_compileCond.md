<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/Conditions.lean :: Light.Compiler.decides_compileCond -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Compiled condition decides its test

**Claim.** For a framed machine memory representing a bounded light state, if the code at `pos` contains the compiled condition and the condition is safe and fits in the frame, then its compiled code decides whether the condition holds: execution takes at most the condition's size, reaches `pos` plus that size when the condition holds and the target `l` otherwise, and changes memory only in the condition's scratch cells.

**Proof.** Split on the form of the condition. In the equality case, the compiled equality-test result establishes the required execution and scratch-memory agreement; in the strict-inequality case, the corresponding compiled less-than result does so. These are exactly the two constructors of conditions, and their value propositions are the respective meanings of `Cond.Holds` (`Light.Compiler.decides_eq`, `Light.Compiler.decides_lt`).

**Key facts.** `Light.Compiler.decides_eq`, `Light.Compiler.decides_lt`.
