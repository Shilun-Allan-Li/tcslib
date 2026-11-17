<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFARM/Machine.lean :: Complexity.LogProg.TQBFARM.St.toV_Z -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Scratch Register Lookup

**Claim.** In the register vector ordered by the seven registers, the entry at index $4$ equals the value of the scratch register.

**Proof.** The register vector lists the state fields in order, and the copy-loop scratch register $Z$ occupies position $4$. Thus its entry at index $4$ is $Z$.
