<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/NDHost.lean :: Turing.guessRunTM_runWith_live -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Liveness before the time bound

**Claim.** For every Boolean word of length less than $T_P+2m+9$, the guess-and-run machine has not halted after processing that word.

**Proof.** Assume for contradiction that the machine halts after processing a word $w$ shorter than the stated bound. Append enough false bits to make a word of length exactly $T_P+2m+9$. By the handoff theorem `guessRunTM_runWith_handoff`, processing this extended word from the initial configuration ends in the live run phase at $q_{\mathrm{entry}}$. On the other hand, once a machine is halted, any further input leaves its configuration unchanged (`NDTM.runWith_of_halt`); decomposing the extended word into $w$ and its appended suffix (`NDTM.runWith_append`) therefore says the final configuration is the supposedly halted configuration. Its state cannot both be none and be the run-phase state, a contradiction.

**Key facts.** `Turing.guessRunTM_runWith_handoff`, `Turing.NDTM.runWith_append`, `Turing.NDTM.runWith_of_halt`.
