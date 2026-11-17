<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathHardMachine.lean :: Complexity.PathHard.preS_A -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Program Precondition

**Claim.** For every choice of the parameters, oracle, input, and program configuration, the configuration satisfies the program precondition: register comparisons have distinct registers, input-payload comparisons have the required valid encoding, and oracle calls use pairwise distinct argument registers.

**Proof.** If the configuration has no instruction state, the precondition holds by definition. Otherwise inspect the current instruction. At copy instructions, expanding the copy routine reduces the precondition to inequalities between the destination and source registers; checking the finitely many copy cases verifies these inequalities. At the incremented-copy instructions the precondition is automatic. For shift, subtraction, and halving routines, inspect their finitely many phases: each phase either has no condition or compares registers whose indices are visibly distinct. The comparison routine likewise has distinct comparison registers in every phase. All remaining instruction forms either impose no condition or call for a direct check of their defining cases. Thus every possible instruction satisfies the precondition, independently of the register contents and input.
