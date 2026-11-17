<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clRead_rewind -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rewinding the target head

**Claim.** Starting in rewind control with target head at $j-1$, after $j+1$ steps the reader reaches completed control, leaves both tapes unchanged, keeps stream cursor $s$, and puts the target head at zero, provided $j\le |w|$.

**Proof.** Induct on $j$. When $j=0$, the target head is at $-1$. The rewind-control transition sees no symbol there, so it moves the target head right and switches directly to completed control; the stream cursor does not move, and the target head becomes zero. For the successor case, the target head starts at $j$. Since $j<|w|$ follows from the induction hypothesis’s bound applied to the successor, the buffer at that position contains $w[j]$. In rewind control, seeing a symbol causes one leftward move on the target tape while preserving the rewind control and leaving the stream head fixed. Thus the first step takes the configuration to the rewind configuration with head at $j-1$. The induction hypothesis then completes the rewind in $j+1$ further steps. Together these are $(j+1)+1$ steps, and the final state and heads are as claimed. Natural-position buffer lookup uses `FinTM.bufferTape_nat`; the run equations split off the first transition via `runFrom_succ_eq_step` and `runFrom_zero`, and the input head stays fixed by `moveInputPos_zero`.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`, `Turing.FinTM.bufferTape_nat`, `Turing.moveInputPos_zero`.
