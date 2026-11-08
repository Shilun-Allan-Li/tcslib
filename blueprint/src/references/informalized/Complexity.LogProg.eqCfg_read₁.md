<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/Frag.lean :: Complexity.LogProg.eqCfg_read₁ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Scanned Symbol After Head Repositioning

**Claim.** In the configuration obtained by placing both distinct register heads at position $k$, the symbol scanned on register $r_1$ is the content of register $r_1$ at cell $k$ in the original configuration.

**Proof.** By definition, the repositioned configuration retains the original tape contents and sets the head position of $r_1$ to $k$. Evaluating the tape at that head therefore gives the original tape's content at cell $k};$ the update to the other head does not affect this position because the registers are distinct.
