<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARM.lean :: Complexity.LogProg.nastep_none -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A halted configuration is fixed by one step

**Claim.** For every choice bit, register valuation, and optional result, one step from the halted configuration leaves it unchanged.

**Proof.** A halted configuration has no control state. By the definition of the nondeterministic step, this case returns the halted state, register valuation, and result unchanged.
