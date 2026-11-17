<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ExpBFS/Run.lean :: Complexity.LogProg.ExpBFS.cp_ne -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Distinct Copy Registers

**Claim.** At every copy site, the source and destination registers are distinct, and neither is the scratch register.

**Proof.** Exhaust the finitely many forms of a copy site. For the radius-copy form, further split on the three phases; the source and destination are then the phase’s radius register and the width register. In each remaining form, unfold the source and destination assignments; for memory-access sites, also split on the site constructor to identify its index register. The resulting register indices are explicit distinct elements of the finite register set, so each of the three inequalities follows by checking those values.
