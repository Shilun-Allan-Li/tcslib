<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARM.lean :: Complexity.LogProg.narun_halted -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Halting is preserved throughout a run

**Claim.** Starting from a halted configuration with register valuation $v$ and result $r$, running on any finite choice string leaves the configuration unchanged.

**Proof.** Induct on the choice string. For the empty string the run returns its starting configuration. For a string $b::\sigma$, a halted configuration remains halted after the first step, with the same registers and result, by the definition of the nondeterministic step. The induction hypothesis applied to the remaining string therefore leaves that same configuration unchanged.
