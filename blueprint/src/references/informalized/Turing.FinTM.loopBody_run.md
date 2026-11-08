<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.loopBody_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exact Simulation Before Stopping

**Claim.** Under the stated liveness and anchor-avoidance hypotheses at every time before $t$, the stop wrapper run from the embedded starting configuration reaches the embedded body configuration at time $t$, with the release bit retained only at time zero and the flag set exactly when the body has halted.

**Proof.** Proceed by induction on $t$. At time zero the wrapper configuration is its prescribed embedding: the body configuration and its release bit are unchanged, and the flag cell is empty. For the successor step, assume the claimed description at time $t$. By the liveness hypothesis the body is in some state $q$ then. The anchor hypothesis shows that the wrapper's stop condition cannot hold: if $t=0$, the hypothesis forces the release bit to be true; if $t>0$, it ensures that the body state is not the anchor. Thus the wrapper takes its ordinary transition. The one-step simulation fact (`loopBody_step`) says this transition matches the body's next step, resets the release bit to false, and writes a true flag exactly if that next body configuration is halted, preserving the prior flag otherwise. Applying the successor-time equation for iteration (`Turing.MultiTapeTM.runFrom_succ_eq_step'`) identifies this with the desired run at time $t+1$.

**Key facts.** `Turing.FinTM.loopBody_step`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`.
