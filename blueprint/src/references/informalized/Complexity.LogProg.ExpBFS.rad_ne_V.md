<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ExpBFS/Run.lean :: Complexity.LogProg.ExpBFS.rad_ne_V -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Radius Register Separation

**Claim.** For every phase among the first search, second search, and final scan, the target register differs from the register assigned as the radius in that phase.

**Proof.** There are three phases. The radius register is $r_s$ in the first and final phases, and $r_{s1}$ in the second. The target register $r_V$ is distinct from both of these register indices, so it differs from the radius register in every phase.
