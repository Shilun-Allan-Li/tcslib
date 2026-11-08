<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Nondeterministic.lean :: Turing.NDTM.runWith_cons -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Runs Under a Leading Choice Bit

**Claim.** Running under the word formed by placing $b$ before $w$ is the same as taking the $b$-step first and then running under $w$.

**Proof.** This follows directly from the recursive definition of a run on a nonempty choice word: its first bit determines the initial step, and the remainder is run from the resulting configuration.
