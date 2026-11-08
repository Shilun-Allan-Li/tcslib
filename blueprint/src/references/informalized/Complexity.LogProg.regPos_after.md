<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/Sim.lean :: Complexity.LogProg.regPos_after -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Register position after a track move

**Claim.** Under the stated hypotheses, the register position at segment index $G1$ and track position $T2$ is the position at index $s$ and track position $tp$, adjusted by $mv$ exactly for the selected current argument register when $s\ne0$.

**Proof.** First, the selected register at a positive segment index $s$ is the argument at index $s-1$ (`segReg_eq`). If $r$ is not in the argument list, its position is always its initial work-tape position, so both sides agree and the adjustment is zero. Now suppose $r$ is an argument register. Its index in the list identifies its segment: the no-repetitions hypothesis ensures that the register is at the current segment precisely when its list index plus one equals $s$ and $s\ne0$. If $G1=s$ and the track position changes by $mv$, the current register’s position changes by exactly that amount, while registers belonging to earlier or later segments stay at their respective right or left boundaries. If instead $mv=0$ and the indices differ by one, the hypotheses place the track at the right boundary of one segment and the left boundary of its neighbor. Those two boundary positions coincide under the register-position rule: the register just completed remains at its word’s right end, and the next register begins at the left end. In each case, splitting according to whether the register is before, at, or after the relevant segment gives the asserted equality.

**Key facts.** `Complexity.LogProg.segReg_eq`.
