<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/ARMSim.lean :: Complexity.LogProg.haltsWith_of_rejects -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rejection implies bounded halting

**Claim.** If the compiled program rejects from the specified initial configuration with register $r$ reset to zero and $W\ge0$, then it halts with output false and all work-head positions in $[-1,W]$; every earlier configuration is between ordinary machine steps and obeys the same head bounds.

**Proof.** Unpack the rejection witness, which supplies a halting time, the false output, the final head-position update, and a description of each earlier configuration as an ordinary-step configuration with register $r$ at zero. The final head-position condition follows from the witness's update equality: the updated register position is zero, while the other positions retain their original nonnegative positions, all at most $W$ since $W\ge0$. For an earlier time, use its witness configuration description and the intermediate-configuration bound (`mid_xCfg`), with the given fact that the program is not at a call state and the position of register $r$ is zero. This yields the required between-step property and bounds for all heads. These facts, together with the rejection witness's halting and output clauses, are exactly the asserted bounded-halting conclusion.

**Key facts.** `Complexity.LogProg.mid_xCfg`.
