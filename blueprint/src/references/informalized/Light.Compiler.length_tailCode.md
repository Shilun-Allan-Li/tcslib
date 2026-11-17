<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/ProgramCode.lean :: Light.Compiler.length_tailCode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Tail Code Length

**Claim.** For every Boolean flag $d$ and natural number $p$, the tail code has length $5$ if $d$ is true and length $2$ if $d$ is false.

**Proof.** Split on the Boolean flag. If it is true, the code contains the initial instruction followed by four instructions in the conditional branch, for a total of five. If it is false, it contains the initial instruction followed by the single accept instruction, for a total of two. The position affects only a branch destination and hence not the length.
