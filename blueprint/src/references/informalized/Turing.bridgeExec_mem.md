<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/MathlibBridge.lean :: Turing.bridgeExec_mem -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Execution State of a Supported Statement

**Claim.** When $q$ belongs to the finite statement support of the compiled program, the optional execution control state determined by $q$ and $v$ is the execution state carrying $q$ together with $v$.

**Proof.** The execution-state construction returns the execution state containing the supported statement and register value whenever its statement argument lies in the program's finite support. Since $h$ supplies precisely that membership, the membership branch applies, giving the stated optional execution state.
