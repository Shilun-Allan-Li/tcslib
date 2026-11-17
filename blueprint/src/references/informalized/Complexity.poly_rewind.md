<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/TMSAT.lean :: Complexity.poly_rewind -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rewinding a Loop Head

**Claim.** From the rewind state with head $i$ at $j-1$, after $j+1$ steps the machine reaches $\mathrm{advance}_{i+1}$ with head $i$ at $0$, leaving the other heads, tapes, and output unchanged.

**Proof.** Induct on $j$. At $j=0$, the head is at $-1$, so its tape cell is blank. The rewind transition moves it one step right and enters $\mathrm{advance}_{i+1}$; the head is now at $0$. For the successor case, when the head is at $(j+1)-1=j$, with $j<q$, that cell contains a $1$. The transition therefore moves the head one step left and remains in rewind, producing the configuration with head at $j-1$. The induction hypothesis handles the remaining $j+1$ steps. The run recurrence combines the initial transition with that remaining run; throughout, no tape or output is changed.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`, `Complexity.polyMove_apply`.
