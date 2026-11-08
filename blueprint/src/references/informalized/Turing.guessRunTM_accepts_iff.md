<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/NDHost.lean :: Turing.guessRunTM_accepts_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Acceptance Criterion for Guess and Run

**Claim.** For every choice-word length meeting the stated bound, the guess-and-run machine has a choice word that halts with output $[\mathrm{true}]$ exactly when some length-$m$ word leads $Q$ to a first accepting verdict with empty output.

**Proof.** For the forward implication, take a choice word whose run halts with output $[\mathrm{true}]$. Extract the length-$m$ guessed word from the portion beginning after the first $T_P+1$ choice bits. The hypothesis on $Q$ supplies a time $T_Q\le T$ when its run on that word first reaches either verdict. The run-and-verdict simulation (`guessRunTM_runWith`) expresses the final output as the simulated run's output followed by the verdict bit. Since the actual output is the singleton $[\mathrm{true}]$, the verdict must be acceptance and the simulated output must be empty; the same simulation identifies the required first-verdict condition. For the reverse implication, take a length-$m$ word and accepting time with empty output. The bound on $Q$ supplies its first verdict time. This time must equal the given accepting time: if either were earlier, the corresponding first-verdict hypothesis would be contradicted. Construct a choice word by placing $T_P+1$ false bits first, then the chosen word, then enough false bits to reach length $B$. The guessed segment is therefore exactly the chosen word, and the size hypothesis ensures enough bits remain for the simulation. Applying `guessRunTM_runWith` shows that the machine halts and appends the acceptance bit to the empty output, giving precisely $[\mathrm{true}]$.

**Key facts.** `Turing.guessRunTM_runWith`.
