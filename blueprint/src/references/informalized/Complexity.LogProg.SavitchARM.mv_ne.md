<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/SavitchARM/Run.lean :: Complexity.LogProg.SavitchARM.mv_ne -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Distinct move registers

**Claim.** For every move operation, its source register differs from its destination register.

**Proof.** Split into the finitely many move-operation cases, and in the parameterized cases also split on the Boolean flag. In each case, the definitions reduce the source and destination to distinct register indices among the listed registers, so their inequality follows directly.
