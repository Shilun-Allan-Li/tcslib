<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.emitterP2_body_prepare -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Preparation Phase Completion

**Claim.** The preparation phase reaches state $8$ with flag recording whether $|w|<|s|$, while retaining $s$ on the candidate and width tapes and placing the suffix of $w$ after its first $|s|$ bits on the length tape. It does so within the stated bound and avoids the anchor through that time.

**Proof.** The preparation machine first supplies a time $t$ at which its own run has the claimed terminal configuration and bound, and at which it has not yet entered state $8$. The controller simulates this preparation machine on the three designated tapes. The phase-simulation lemma carries the preparation machine's run to the controller, and its guard is exactly the fact that no state with preparation index $8$ occurs before the endpoint. The small-frame identity then identifies the simulated tapes with the controller's bank layout: the candidate remains $s$, the width bank contains $s$, and the length bank contains $w$ with its first $|s|$ entries dropped. The terminal flag is the preparation machine's recorded truth value of $|w|<|s|$. The same phase simulation ensures that the controller has not visited the anchor during this run.

**Key facts.** `Turing.FinTM.emitterP2_prepare_first`, `Turing.FinTM.emitterP2_phase`, `Turing.FinTM.emitterP2_small_frame`.
