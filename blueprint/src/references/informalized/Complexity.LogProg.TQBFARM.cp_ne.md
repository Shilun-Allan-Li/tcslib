<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFARM/Machine.lean :: Complexity.LogProg.TQBFARM.cp_ne -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Distinct Registers in Copy Operations

**Claim.** At every copy-operation site, the selected source and destination registers are distinct, and neither is the scratch register.

**Proof.** The copy site has finitely many constructors. For each constructor, the source and destination are among the specified register indices; checking these indices shows that they differ from one another and from the scratch register. The Boolean parameters in the return and literal sites do not affect those indices, so their two possible values give the same verification.
