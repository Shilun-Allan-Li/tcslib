<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/MARMCompile.lean :: Complexity.LogProg.mcompileTM_init -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial configuration of the compiled machine

**Claim.** The compiled machine's initial configuration on input $x$ is the configuration with start label $l_0$, all register values zero, memory identically false, memory-head position zero, and empty output.

**Proof.** Both configurations have the same state, input-head position, and output: the initial state is the program start label paired with the start phase, the input head is at its initial position, and the output is empty. Compare the work tapes by separating the final memory tape from all earlier tapes. On the memory tape, the initial Boolean memory is identically false, so its encoded contents are nowhere marked, and its head is at zero. Among the earlier tapes, the seam construction divides them into registers and decider tapes. Each register stores the binary representation of zero, which is empty, and every decider tape is blank; all their head positions are zero. Hence the work-tape contents and positions agree at every index, proving equality of the configurations.
