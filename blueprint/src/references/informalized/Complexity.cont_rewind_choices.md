<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.cont_rewind_choices -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rewinding the Choice Buffer

**Claim.** Starting in loader state $5$ with choice-buffer head at $j-1$, after $j+1$ steps the loader reaches the embedded initial configuration of $N$ with boundary tag true, choice word $u$, choice-head index $0$, and unchanged physical input position.

**Proof.** Induct on $j$. When $j=0$, the choice tape is blank at the head, so the state-$5$ transition enters the simulation core immediately. The run identities for zero and one step (`Turing.MultiTapeTM.runFrom_zero` and `Turing.MultiTapeTM.runFrom_succ_eq_step`) reduce the claim to that transition; the stationary input-head movement is justified by `Turing.moveInputPos_zero`. For the successor case, the head is at index $j$, where the choice tape contains $u[j]$ because $j<|u|$, a consequence of the hypothesis $j+1\le |u|$. The state-$5$ transition consumes that symbol and moves the choice head one position left, leaving the other configuration data unchanged. Thus one step changes the starting configuration for the remaining run to the state-$5$ configuration with head at $j-1$. The run-successor identity reduces the total run to this step followed by $j+1$ steps, and the induction hypothesis finishes the argument.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`, `Turing.moveInputPos_zero`.
