<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFARM/Machine.lean :: Complexity.LogProg.TQBFARM.preS_A -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Program instruction precondition

**Claim.** For every input and configuration, the fixed program selects an instruction satisfying its precondition: register comparisons use distinct registers, input-word comparisons have valid encodings, and oracle calls have distinct argument registers.

**Proof.** If the configuration is halted, its precondition holds automatically. Otherwise inspect the control label and hence the instruction selected by the program. Most labels select instructions whose preconditions are automatic. At the parameterized loop labels, checking the finitely many phases identifies only the corresponding elementary instruction; splitting on the Boolean parameters resolves the conditional exits. The remaining conditional cases are checked directly from their branches. Thus no selected instruction violates the required distinctness or input-validity conditions, and all oracle calls use their specified singleton argument list, whose register entries are distinct.
