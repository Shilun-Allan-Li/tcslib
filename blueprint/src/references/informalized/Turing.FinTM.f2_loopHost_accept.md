<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_loopHost_accept -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Loop host halting bound

**Claim.** The loop host halts within $2|u|+3$ steps and has output $u$ in find mode and $[\mathrm{true}]$ otherwise.

**Proof.** Let the prescribed starting configuration be the base configuration. The call-to-frame identity (`f2_loopCall_frame`) expresses it as a control frame in phase 7, with the flag tape containing true and the payload tape holding the output word $u$. One host step therefore takes the non-find branch directly to a halted state while emitting true. In find mode, that step enters phase 12 and rewinds the payload head; the rewind identity (`f2_loopHost_payload_rewind`) takes $|u|+1$ steps to reach phase 13 with the head reset. The replay identity (`f2_loopHost_frame_replay`) then emits the stored word and halts in another $|u|+1$ steps. Including the initial step gives $1+(|u|+1)+(|u|+1)=2|u|+3$. The run concatenation and successor-step identities (`runFrom_add`, `runFrom_succ_eq_step`) justify splitting the run into these segments.

**Key facts.** `Turing.FinTM.f2_loopCall_frame`, `Turing.FinTM.f2_loopHost_payload_rewind`, `Turing.FinTM.f2_loopHost_frame_replay`, `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_add`.
