<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/SpaceAmplifyPolyMachine.lean :: Randomized.PolyAmp.ampA_npreS -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Preconditions of the Amplification Program

**Claim.** For every choice of parameters, input, and configuration, resolving every choice in the amplification program in favor of false satisfies its precondition.

**Proof.** Write the configuration as a program location, register values, and result. If its location is absent, the precondition holds directly. Otherwise inspect the instruction at that location, with the Boolean parameter distinguishing the two program variants. The only nontrivial preconditions concern comparisons of distinct registers, validity of the input for input-dependent branches, and distinctness of arguments to calls. In the false-resolved program, a choice instruction becomes a return instruction, which has no such precondition; inspection of the remaining instruction forms shows that each required condition is either automatic or satisfied by the form of the instruction. Hence the precondition holds in every case.
