<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/SavitchARM/Machine.lean :: Complexity.LogProg.SavitchARM.St.toV_Z -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Scratch Register Coordinate

**Claim.** For a state of the Savitch machine, coordinate $5$ of its 18-entry register vector equals its copy-and-shift-loop scratch register $Z$.

**Proof.** By definition, the register vector lists the state coordinates in order, with $Z$ in position $5$ when indexing starts at $0$. Since $r_Z=5$, evaluating the vector at $r_Z$ gives $Z$.
