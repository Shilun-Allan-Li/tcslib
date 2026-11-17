<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Contract/Embed.lean :: Turing.Contract.embed_positive -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positivity under tape embedding

**Claim.** If a contract for a machine with $m$ work tapes has strictly positive duration on every admissible run, then its embedding into $k$ work tapes also has strictly positive duration on every admissible run.

**Proof.** Fix an admissible datum and starting configuration for the embedded contract. Its duration is, by the definition of the embedding, the original contract's duration on the selected configuration. That selected configuration has the required entry state and satisfies the original precondition, so positivity of the original contract makes this duration strictly positive.
