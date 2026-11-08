<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/SavitchARM/Machine.lean :: Complexity.LogProg.SavitchARM.St.toV_E -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Popped endpoint coordinate

**Claim.** For every machine state, the register-vector coordinate indexed by the popped endpoint equals the popped endpoint register.

**Proof.** The register vector lists the popped endpoint as its seventeenth entry, and the popped-endpoint index selects that entry. The selected coordinate is therefore exactly the popped endpoint register.
