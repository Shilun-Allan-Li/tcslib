<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/NDHost.lean :: Turing.guessRunTM_haltsWithin -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Halting Bound for Guess and Run

**Claim.** Under the stated hypotheses, the guess-and-run machine halts on every choice-bit word of length $T_P+2m+T+11$.

**Proof.** Take any choice word of that length and extract the $m$-bit segment after the first $T_P+1$ bits. By the hypothesis on $Q$, this word has a first accepting or rejecting verdict at some time $T_Q\le T$. The length is therefore at least $T_P+2m+T_Q+11$. The run-and-verdict simulation theorem (`guessRunTM_runWith`) applies: after the setup, bounded guess, and rewind, the machine simulates $Q$ through that verdict and halts. Thus the chosen word leads to a halted configuration, as required for every word of the specified length.

**Key facts.** `Turing.guessRunTM_runWith`.
