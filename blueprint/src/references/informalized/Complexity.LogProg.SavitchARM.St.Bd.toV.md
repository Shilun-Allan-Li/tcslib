<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/SavitchARM/Machine.lean :: Complexity.LogProg.SavitchARM.St.Bd.toV -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Register vector respects the bound

**Claim.** If all eighteen registers of a machine state are at most $B$, then every coordinate of its register vector is at most $B$.

**Proof.** Write the eighteen register bounds supplied by the hypothesis. The register vector lists those same registers in order. For any coordinate, its index selects one of the eighteen entries, and the corresponding bound from the hypothesis applies. Thus every coordinate is at most $B$.
