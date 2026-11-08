<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.b2_rewind_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rewinding to the Guessing Phase

**Claim.** For $j\le |x|$, running the reverse host on any choice word of length $j+1$ from loader state $1$, input-head position $j$, assembly buffer $x$, and assembly-head position $|x|$ reaches the guessing-phase configuration with the input-normalized scheduler initialized on $x$ and empty guessed word.

**Proof.** Induct on $j$, generalizing the choice word. When $j=0$, the word has one bit, and the terminal rewind step sends the loader configuration at input position $0$ directly to the desired guessing-phase configuration (`Complexity.b2_rewind_done`). For the induction step, write the word as a first bit followed by a tail. The run on the whole word is the run on the tail after the first step (`Turing.NDTM.runWith_cons`). Since $j<|x|$, the one-step rewind fact (`Complexity.b2_rewind_step`) moves the input head from $j+1$ to $j$ while leaving the other configuration data unchanged. The tail has length $j+1$, so the induction hypothesis applies from this new loader configuration and gives the claimed endpoint.

**Key facts.** `Complexity.b2_rewind_done`, `Turing.NDTM.runWith_cons`, `Complexity.b2_rewind_step`.
