<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARM.lean :: Complexity.LogProg.narun_append_of_halted -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Choice strings after halting

**Claim.** If the run on a choice string has halted, appending any further choices leaves its final configuration unchanged.

**Proof.** By the concatenation law (`narun_append`), the run on $\sigma++\tau$ is the run on $\tau$ starting from the configuration reached after $\sigma$. That configuration has no active label by hypothesis. A halted configuration is fixed by every further run (`narun_halted`), regardless of its register values or recorded result. Thus the appended choices do not change the configuration.

**Key facts.** `Complexity.LogProg.narun_append`, `Complexity.LogProg.narun_halted`.
