<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/ParsePlain.lean :: Complexity.LogProg.rewind_x -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rewinding the Input Head

**Claim.** Under the stated transitions at $rw_1$ and $rw_2$, the machine reaches state $nx$ with input-head position $1$ after finitely many steps, without changing register $r$'s head position. Every earlier configuration has a state, retains that register-head position, and is at a non-call state.

**Proof.** First prove the scan statement for a run starting in $rw_2$ at input position $j\le |x|$. Induct on $j$. At $j=0$, the input symbol is absent, so the transition in $rw_2$ moves right and enters $nx$. Since the position was zero, the right-move position formula (`Complexity.LogProg.moveInputPos_pos_val`) gives final position $1$. At times before this one-step endpoint, the only configuration is the starting one, still in the non-call state $rw_2$.

For the successor case, the input symbol is $x[j]$, so the transition moves left and remains in $rw_2$. The negative-move position formula (`Complexity.LogProg.moveInputPos_neg_val'`) lowers the position from $j+1$ to $j$, allowing the induction hypothesis to finish the scan. The one-step run formula (`Complexity.LogProg.rrun_one_x`), together with the transition calculation (`Complexity.LogProg.apply_xAct`), identifies this first move and shows it changes neither the register head nor the other relevant configuration data. The run-composition identities (`Complexity.LogProg.rrun_succ_left` and `Complexity.LogProg.rrun_add`) assemble the steps and transfer the pre-final witnesses.

Finally, the transition at $rw_1$ makes one left move into $rw_2$. Apply the scan result beginning at the resulting input position; it is within the input range because the negative move lowers the original position by one. Add this initial step to the scan duration. Before it, the configuration is at $rw_1$; thereafter, every pre-final witness comes from the scan in $rw_2$. Both states are non-call states by hypothesis, and the register head remains at $p$ throughout.

**Key facts.** `Complexity.LogProg.apply_xAct`, `Complexity.LogProg.moveInputPos_neg_val'`, `Complexity.LogProg.moveInputPos_pos_val`, `Complexity.LogProg.rrun_add`, `Complexity.LogProg.rrun_one_x`, `Complexity.LogProg.rrun_succ_left`.
