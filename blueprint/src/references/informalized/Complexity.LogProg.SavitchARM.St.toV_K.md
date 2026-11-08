<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/SavitchARM/Machine.lean :: Complexity.LogProg.SavitchARM.St.toV_K -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Code bound coordinate

**Claim.** For every machine state, the register-vector coordinate indexed by the code bound equals the code-bound register.

**Proof.** The register vector lists the code-bound register as its tenth entry, and the code-bound index selects that entry. Thus the selected coordinate is the code-bound register.
