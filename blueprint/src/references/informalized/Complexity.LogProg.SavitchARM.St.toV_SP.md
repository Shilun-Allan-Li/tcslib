<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/SavitchARM/Machine.lean :: Complexity.LogProg.SavitchARM.St.toV_SP -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Phase stack register coordinate

**Claim.** For a state of the Savitch machine, the coordinate at index $15$ in its 18-entry register vector equals the value of its phase-stack register $SP$.

**Proof.** The phase-stack register $SP$ is the vector entry at index $15$. Since $r_{SP}$ denotes that index, the selected coordinate equals $SP$.
