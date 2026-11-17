<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/NDHost.lean :: Turing.guessRunTM_runWith_handoff_state -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# State at the verifier handoff

**Claim.** After the guess-and-run machine processes any Boolean word of length $T_P+2m+9$, its state is the run-phase state with underlying state $q_{\mathrm{entry}}$.

**Proof.** Apply the handoff configuration theorem `guessRunTM_runWith_handoff` to the given run of $P$, its first visit to $p_{\mathrm{exit}}$, and the stated tape-block hypotheses. That theorem identifies the resulting configuration as one in the run phase whose underlying machine state is $q_{\mathrm{entry}}$. Taking its state component gives the claimed equality.

**Key facts.** `Turing.guessRunTM_runWith_handoff`.
