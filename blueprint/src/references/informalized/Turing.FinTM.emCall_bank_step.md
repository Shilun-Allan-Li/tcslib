<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.emCall_bank_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One Bank Cleanup Step

**Claim.** For each work tape, the clean-call machine can clear the next bank and advance its cleaner-entry state in at most $6T+8$ steps.

**Proof.** Apply the bounded-cleanup lemma `emCall_clear_first` to tape $i$. It supplies a time $t$ with $0<t\le 6T+7$, no earlier visit to cleaner state $3$, and a run of the three-tape cleaner from state $0$ to state $3$, where all three tapes are blank and all heads are at the origin. Embed those three cleaner tapes into the call machine’s slots for bank $i$. The initial-embedding identity `emCall_bank_initial` identifies this embedded starting configuration with the required bank frame. The cleaner’s transitions agree with the call machine’s transitions on states $0,1,2$; the run-agreement principle (`MultiTapeTM.runFrom_mapState_of_agreeOn`) therefore transports the run up to time $t$, using the no-earlier-visit property to ensure the source state remains among those on which transitions agree. The embedding-run identity (`embedEmitTM_runFrom`) identifies the transported run with the embedded cleaner run. At time $t$, `emCall_bank_final` identifies the resulting embedded state-$3$ configuration with the bank frame in which bank $i$ has been cleared. One additional call-machine transition advances from that state to the cleaner-entry state for bank $i+1$ while leaving the frame contents and heads as required. Thus the total time is $t+1\le 6T+8$; the run concatenation law (`runFrom_succ_eq_step'`) and the fact that a zero input-head move preserves its position (`moveInputPos_zero`) give the stated endpoint.

**Key facts.** `Turing.FinTM.emCall_clear_first`, `Turing.MultiTapeTM.runFrom_mapState_of_agreeOn`, `Turing.embedEmitTM_runFrom`, `Turing.FinTM.emCall_bank_initial`, `Turing.FinTM.emCall_bank_final`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.FinTM.controlAction_apply`, `Turing.moveInputPos_zero`.
