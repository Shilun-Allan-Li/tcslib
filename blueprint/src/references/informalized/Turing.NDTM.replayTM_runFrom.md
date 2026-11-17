<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/ChoiceReplay.lean :: Turing.NDTM.replayTM_runFrom -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Replaying a Choice Word

**Claim.** For each $t\le |s|$, there is a replay head position $p\le t$ such that, if the simulated run after the first $t$ bits has not halted, then $p=t$, and the replay machine after $t$ steps has the same simulated configuration, the unchanged choice tape, and head position $p$.

**Proof.** Induct on $t$. At $t=0$, take $p=0$: the replay machine and the original configuration agree initially, and the position bound and implication are immediate.

Suppose the assertion holds at $t$, and extend to $t+1$. The first $t+1$ symbols of $s$ consist of its first $t$ symbols followed by the symbol $s_t$ (`List.take_succ_eq_append_getElem`). Apply the induction hypothesis to obtain a matching replay configuration and position $p$. If the simulated machine is already halted after $t$ steps, it remains at that configuration under every further choice word (`Turing.NDTM.runWith_of_halt`), and the replay machine's deterministic step also leaves its configuration unchanged (`Turing.MultiTapeTM.step_of_halt`). Keep the same head position $p$, which remains at most $t+1$; the implication concerning a live final run is vacuous because the run is halted.

If instead the simulated state is some $q$, the induction hypothesis's live-run condition forces $p=t$. The replay choice head is therefore at the next symbol, and the choice-tape definition makes that symbol $s_t$ (`FinTM.bufferTape`). Its other work tapes and input symbol match those of the simulated configuration. Consequently, the replay transition reads exactly the choice used by the original machine at step $t+1$, and performs the same transition on the simulated tapes and state. The replay machine leaves its added choice tape unchanged and advances its head to $t+1$. Taking the new position to be $p+1$ proves the required bound and gives the asserted configuration equality.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.NDTM.runWith_append`, `Turing.NDTM.runWith_of_halt`, `Turing.MultiTapeTM.step_of_halt`, `Turing.NDTM.runWith_cons`, `Turing.NDTM.runWith_nil`.
