<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.emitterP2_body_advance -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Candidate advancement in the controller

**Claim.** From the advance phase with candidate $s$ installed, the controller reaches its return state with the candidate updated by appending one $1$ exactly when $|s|\le |w|$, within the stated time bound and without visiting the anchor.

**Proof.** First analyze the auxiliary restore machine. Its run starts from the configuration identified with the controller's advance state and reaches state $(4,\mathrm{false})$ with the updated candidate and all other relevant tapes blank, within the bound; before then it avoids that auxiliary machine's terminal state (`splitRestore_first`). The phase simulation lemma transfers this run to the controller: while the auxiliary states remain outside their terminal state, the controller's transitions agree with the embedded auxiliary transitions, and the embedded configurations retain the same tape contents (`emitterP2_phase`). The initial configuration is identified with the auxiliary start (`emitterP2_advance_initial`); the one-tape embedding and the one-tape state-word identity translate the simulated configurations back to the controller's layout (`emitterP2_one_frame`, `emitterP2_stateWord_one`). Updating the candidate slot converts the resulting tape update into the stated candidate `splitStep` (`emitterP2_update_candidate`). Together these give the desired time bound, endpoint, and anchor avoidance.

**Key facts.** `Turing.FinTM.splitRestore_first`, `Turing.FinTM.emitterP2_phase`, `Turing.FinTM.emitterP2_advance_initial`, `Turing.FinTM.emitterP2_one_frame`, `Turing.FinTM.emitterP2_stateWord_one`, `Turing.FinTM.emitterP2_update_candidate`.
