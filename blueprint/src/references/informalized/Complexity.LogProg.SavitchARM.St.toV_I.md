<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/SavitchARM/Machine.lean :: Complexity.LogProg.SavitchARM.St.toV_I -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Level coordinate

**Claim.** For every machine state, the register-vector coordinate indexed by the level equals the level register.

**Proof.** The register vector lists the level register as its fourteenth entry, and the level index selects that entry. Hence the selected coordinate equals the level register.
