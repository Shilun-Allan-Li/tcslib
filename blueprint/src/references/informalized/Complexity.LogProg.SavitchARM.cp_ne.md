<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/SavitchARM/Run.lean :: Complexity.LogProg.SavitchARM.cp_ne -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Disjoint Copy Registers

**Claim.** For every copy-loop site, the source and destination registers are distinct, and neither is the copy routine's scratch register.

**Proof.** The copy sites are a finite list of constructors, with one Boolean choice at the sites that carry a Boolean parameter. Checking each constructor and each such choice reduces the claims to inequalities between the fixed register indices. Those indices are pairwise different in each required comparison, so all three inequalities hold.
