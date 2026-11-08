<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyProgram.lean :: BoolCircuit.progRun_append -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Concatenation law for program execution

**Claim.** Executing a concatenation of instruction lists $p$ and $q$ from an initial block state gives the same result as executing $p$ first and then executing $q$ from the resulting state.

**Proof.** Program execution is a left fold over the instruction list: each instruction appends its computed block to the current state. Folding over a concatenated list is the same as first folding over its prefix $p$, then folding over its suffix $q$ from the state produced by that prefix. Hence executing $p++q$ from the initial state equals executing $q$ from the result of executing $p$.
