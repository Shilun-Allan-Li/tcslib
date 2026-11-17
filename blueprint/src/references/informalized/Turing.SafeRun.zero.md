<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/EmitIterEmbed.lean :: Turing.SafeRun.zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero-Step Safety

**Claim.** For any multi-tape machine, forbidden state, and configuration $c$, the run from $c$ for zero steps is safe and ends at $c$.

**Proof.** A run of zero steps leaves the configuration unchanged, so its endpoint is $c$. There are no natural numbers strictly less than zero, hence there is no time at which the safety condition needs to be checked.
