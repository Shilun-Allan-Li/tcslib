<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LogspaceUniformAdj.lean :: BoolCircuit.AdjWalk.preS_walk -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Validity of Walk Instruction Checks

**Claim.** For a valid plain input and any configuration, the walk instruction selected at its current state satisfies the precondition checks: register comparisons use distinct registers, input-word comparisons have valid input, calls have distinct argument registers, and all other instruction checks hold automatically.

**Proof.** If the configuration has no current label, its precondition is automatic. Otherwise inspect the current label. The walk's only register comparison is at `aL`, where it compares registers $2$ and $1$, which are distinct; the comparison at `uL` and `oL` likewise uses registers $3$ and $2$, or $3$ and $1$, respectively, also distinct. Each input-word comparison occurs at a label of the form `em s` and is a comparison with the plain input word, so its required validity is exactly the assumed validity of the input. The only calls use either the singleton argument list $[1]$ or the list $[2,1]$, each without repetitions. Every other instruction has no additional precondition, so the checks hold in all cases.
