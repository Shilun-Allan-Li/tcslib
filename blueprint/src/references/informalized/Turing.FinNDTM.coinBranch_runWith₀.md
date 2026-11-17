<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/NDCombinators.lean :: Turing.FinNDTM.coinBranch_runWith₀ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Run preserves the first branch

**Claim.** Starting from a configuration of $N_0$ embedded in the first branch, running the combined machine under $w$ yields the embedding of the configuration reached by running $N_0$ from that configuration under $w$.

**Proof.** Induct on the choice word $w$, allowing the starting configuration to vary. For the empty word, neither machine takes a step, so the claim is the identity. For a word beginning with $b$, express each run as the run on the tail after one $b$-step (`runWith_cons`). The one-step preservation theorem for the first branch (`coinBranch_stepWith₀`) identifies the combined machine's first step with the embedding of $N_0$'s step. The induction hypothesis, applied to that resulting configuration and the tail word, then identifies the remaining runs, proving the equality.

**Key facts.** `Turing.NDTM.runWith_cons`, `Turing.FinNDTM.coinBranch_stepWith₀`.
