<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/QueryReshape.lean :: Complexity.comp_preS -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Machine Instruction Admissibility

**Claim.** For every choice of the natural parameters, mode, input, and machine configuration, the active instruction satisfies its admissibility precondition: register-equality tests compare distinct registers, input-word comparisons occur only on inputs of the required canonical form, and oracle calls use pairwise distinct argument registers.

**Proof.** If the configuration is halted, its precondition holds immediately. Otherwise, inspect the active machine state and the instruction assigned to it. In the copy states, the only nontrivial check is that the source and destination registers listed for each of the eight copy stages are distinct; the finite list of stages verifies this directly. In the scan and second-scan states, the limit register differs from register 0, and the remaining parameterized states reduce to the same direct checks of the register indices. The other states either issue instructions with no admissibility side condition, or their argument-register lists are visibly free of repetitions. Thus every possible active instruction meets its precondition, independently of the input.
