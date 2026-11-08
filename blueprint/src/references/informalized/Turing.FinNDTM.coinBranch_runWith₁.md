<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/NDCombinators.lean :: Turing.FinNDTM.coinBranch_runWith₁ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Run preserves the second branch

**Claim.** Starting from a configuration of $N_1$ embedded in the second branch, running the combined machine under $w$ yields the embedding of the configuration reached by running $N_1$ from that configuration under $w$.

**Proof.** Induct on the choice word $w$, allowing the starting configuration to vary. For the empty word, both runs leave their configurations unchanged. If $w$ begins with $b$, rewrite each run as its first $b$-step followed by the run on the tail (`runWith_cons`). The one-step preservation theorem for the second branch (`coinBranch_stepWith₁`) identifies the combined machine's first step with the embedding of $N_1$'s step. The induction hypothesis applied to the resulting configuration and the tail word gives the desired equality of the remaining runs.

**Key facts.** `Turing.NDTM.runWith_cons`, `Turing.FinNDTM.coinBranch_stepWith₁`.
