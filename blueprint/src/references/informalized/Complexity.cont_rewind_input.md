<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.cont_rewind_input -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rewinding the Input Buffer

**Claim.** Starting in loader state $4$ with the input-buffer head at $j-1$ and choice-buffer head at $|u|$, after $j+1$ steps the loader is in state $5$, with the input-buffer head at $0$ and the choice-buffer head at $|u|-1$, while the physical input position and tape contents are preserved.

**Proof.** Induct on $j$. For $j=0$, the input-buffer head is at $-1$, where the buffer tape is blank. The state-$4$ transition therefore moves the input-buffer head right and the choice-buffer head left, entering state $5$; its input-head movement is zero, so the physical input position stays fixed. The run identities for zero and one step (`Turing.MultiTapeTM.runFrom_zero` and `Turing.MultiTapeTM.runFrom_succ_eq_step`) reduce the claim to this transition, with stationary input movement given by `Turing.moveInputPos_zero`. For the successor case, the input-buffer head is at index $j$, where it reads $x[j]$ since $j<|x|$, guaranteed by $j+1\le |x|$. The state-$4$ transition moves that head one position left and stays in state $4$, preserving the other data. The run-successor identity separates this step from the remaining $j+1$ steps; the induction hypothesis then yields state $5$ and the claimed final head positions.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`, `Turing.moveInputPos_zero`.
