<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/SavitchARM/Machine.lean :: Complexity.LogProg.SavitchARM.St.toV_P -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Power accumulator coordinate

**Claim.** For every machine state, the coordinate of its register vector indexed by the power accumulator is equal to the value of its power accumulator register.

**Proof.** The register vector is ordered with the power accumulator immediately after the exponent counter, so its entry at index $3$ is exactly $P$. Since $r_P$ is that index, evaluating the vector there gives the claimed equality directly.
