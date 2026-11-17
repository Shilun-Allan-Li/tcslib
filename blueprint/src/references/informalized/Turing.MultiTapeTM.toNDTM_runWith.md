<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Nondeterministic.lean :: Turing.MultiTapeTM.toNDTM_runWith -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Choice-Independent Run Length

**Claim.** For every finite choice word, running the associated nondeterministic machine from a configuration gives the same result as running the deterministic machine for the length of that word.

**Proof.** Induct on the choice word, allowing the starting configuration to vary. For the empty word, the nondeterministic run returns its starting configuration, as does the deterministic run of length zero. For a word consisting of a first choice followed by a tail, the nondeterministic run first takes the choice-indexed step and then runs on the tail. Both choice transitions of the associated machine are the deterministic machine’s transition, so that first step is exactly one deterministic step. By the induction hypothesis, the tail run from this new configuration equals the deterministic run from it for the tail’s length. The deterministic run decomposition identifies this with the run from the original configuration for one plus the tail length (`runFrom_succ_eq_step`); the corresponding decomposition of `runWith` is `runWith_cons`.

**Key facts.** `Turing.NDTM.runWith_cons`, `Turing.MultiTapeTM.runFrom_succ_eq_step`.
