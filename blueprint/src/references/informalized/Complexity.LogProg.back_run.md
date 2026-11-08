<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/CleanSweep.lean :: Complexity.LogProg.back_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounds During the Return Phase

**Claim.** During the return phase for tape $i$, all work-tape head positions stay within the bound $B$ through time $n+1$, and the configuration at time $n+1$ has the stated next phase, cleared second-bank tape, and reset heads.

**Proof.** Proceed by induction on $n$, keeping the tape contents and head positions as parameters. The return phase moves right over blank cells until it reaches the origin mark; at that mark it erases the mark, resets the two heads on tape $i$ to the origin, and advances to the next cleaning phase (or halts if there is no next tape).

1. If $n=0$, the equation $-D_p(i)=0$ gives $D_p(i)=0$. The mark on tape $i$ is therefore under the head. By the definition of the cleaning machine, its one step performs the reset and phase transition, producing exactly the claimed final configuration. The initial head bound follows from the assumed bound on $D_p$; after the step, the updated head positions satisfy the same bound, using the fact that replacing one position by a value within the bound preserves the pointwise bound (`abs_update_le`). The pointwise bound on configuration head positions follows from the configuration representation (`PB_ccfg`).

2. For the successor case, the head begins on a blank cell, since the origin mark is at $0$ and the head is at $-n<0$. The cleaning transition moves both heads one cell right without changing the tape contents. Write $D_p'$ for the updated positions, with position $i$ increased by one. The hypothesis $a\le D_p(i)$ ensures that this new position remains within the bound, so the bound is preserved for every updated position (`abs_update_le`). The induction hypothesis applies with $n$ decreased by one: the updated head is one step closer to the origin, while the tape contents and origin mark are unchanged. It gives the bound for all subsequent configurations through the target time and the claimed reset configuration at that time. Rewriting the run from its first step as a run from the updated configuration (`runFrom_succ_eq_step`) transfers both conclusions to the original run.

**Key facts.** `Complexity.LogProg.PB_ccfg`, `Complexity.LogProg.abs_update_le`, `Complexity.LogProg.markI_empty`, `Complexity.LogProg.ccfg_state`, `Complexity.LogProg.ccfg_mark`, `Complexity.LogProg.apply_clAct`, `Turing.MultiTapeTM.runFrom_succ_eq_step`.
