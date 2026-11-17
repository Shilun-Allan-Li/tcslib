<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/ARMSim.lean :: Complexity.LogProg.mid_xCfg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Middle invariant after a head update

**Claim.** If the program has no decider call at the chosen state and the updated register head lies between $-1$ and $W$, with $W\ge 0$, then the configuration obtained by setting the state, input-head position, and register-head position as specified satisfies the middle invariant.

**Proof.** The middle invariant requires that the current state have no decider call and that all register heads lie in $[-1,W]$. The configuration's state is the chosen state $s$, so the no-call assumption supplies the first requirement. Register $r$ has head position $q$, which satisfies the bounds by hypothesis. Every other register keeps its seam head position $0$, which also lies in the interval because $W\ge0$. The chosen input-head position does not affect either requirement.
