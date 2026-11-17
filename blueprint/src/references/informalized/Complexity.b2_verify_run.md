<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.b2_verify_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Relocated Verifier Run

**Claim.** For every finite choice word whose proper prefixes leave the verifier nonhalted, the host simulates the verifier for the full word while preserving the scheduler data and maintaining a correct boundary tag.

**Proof.** Proceed by induction on the choice word, allowing the starting verifier configuration and tag to vary. For the empty word, keep the original tag: the run and its encoded verifier-phase configuration are unchanged. For a word beginning with a bit, the verifier is live at the initial configuration by the hypothesis at time zero. Apply the one-step simulation fact (`Complexity.b2_verify_step`) to obtain the successor tag and the matching host configuration after that bit. Every configuration in the remaining verifier run is also live: the run after $s$ steps from the successor is the run after $s+1$ steps from the original configuration, by the successor-time identity (`Turing.MultiTapeTM.runFrom_succ_eq_step`). Thus the induction hypothesis applies to the tail. It supplies a final correct tag and identifies the host's tail run with the encoding of the corresponding verifier run. Finally, the choice-word recursion (`Turing.NDTM.runWith_cons`) says that the whole host run is this tail run after the first host step; the same successor-time identity identifies the final verifier configuration with the run of length $|w|$.

**Key facts.** `Complexity.b2_verify_step`, `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.NDTM.runWith_cons`.
