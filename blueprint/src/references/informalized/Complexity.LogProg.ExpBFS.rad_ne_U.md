<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ExpBFS/Run.lean :: Complexity.LogProg.ExpBFS.rad_ne_U -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Radius Register Separation

**Claim.** For every phase among the first search, second search, and final scan, the source register differs from the register assigned as the radius in that phase.

**Proof.** There are three phases. In the first and final phases the radius register is $r_s$, while in the second it is $r_{s1}$. The source register is $r_U$. Since these register indices are distinct in each case, the asserted inequality follows by checking the three phases.
