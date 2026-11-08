<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/ARMSim.lean :: Complexity.LogProg.mid_regCfg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Register configuration invariant

**Claim.** If the program has no decider call at the chosen state and the updated register head lies between $-1$ and $W$, with $W\ge 0$, then the configuration obtained by replacing register $r$ with the specified tape and head position satisfies the middle invariant.

**Proof.** The middle invariant has two parts. The state of the updated configuration is the chosen state $s$, so the assumption that the program has no call at $s$ gives the first part. For the head bounds, the updated position of register $r$ is $q$, which lies in $[-1,W]$ by hypothesis. Every other register retains its initial head position, namely $0$ in the seam configuration; since $W\ge0$, this too lies in $[-1,W]$.
