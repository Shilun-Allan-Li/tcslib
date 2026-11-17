<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/ARMRun.lean :: Complexity.LogProg.init_eq_aseam -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial configuration as a simulation seam

**Claim.** For any starting state $l_0$, the initial machine configuration on input $x$ with state $(l_0,\mathrm{start})$ equals the seam configuration on $x$ with base state $l_0$, all registers zero, and empty output.

**Proof.** Compare the configuration components. Both have state $(l_0,\mathrm{start})$, input-head position $1$, zero head positions, and empty output. At every tape coordinate, the initial work tape is blank; the seam tape stores the binary representation of zero, which is empty, so its buffer is blank at every coordinate as well. Hence the configurations agree.
