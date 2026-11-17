<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.loop_rewind_bounded -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded Input-Head Rewind

**Claim.** Under the stated transition rules, a machine starting in state $s$ reaches state $d$ with input-head position $1$ in at most $p+2$ steps, without changing the other configuration components.

**Proof.** Take one step from the starting configuration. The rule for state $s$ moves the input head left and puts the machine in state $r$; the other components are unchanged, since this transition is the control action. The new head position is $p-1$, so it is at most the input length. Apply the scan-rewind result to this new configuration: from state $r$, the machine moves left across scanned input symbols and, upon reaching the no-symbol position, moves right and enters $d$. In $c.\mathrm{inputPos}+1$ further steps this reaches position $1$, leaving every other component unchanged. The total time is $1+(p-1+1)=p+1$, which is at most $p+2$. The run-composition law justifies combining the initial step and this subsequent run into one run from the original configuration.

**Key facts.** `Turing.FinTM.controlAction_apply`, `Turing.FinTM.moveInputPos_neg_val`, `Turing.MultiTapeTM.runFrom_add`, `Turing.FinTM.rewind_scan`.
