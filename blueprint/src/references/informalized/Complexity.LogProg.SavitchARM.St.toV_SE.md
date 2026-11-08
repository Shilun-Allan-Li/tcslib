<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/SavitchARM/Machine.lean :: Complexity.LogProg.SavitchARM.St.toV_SE -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Saved endpoints register coordinate

**Claim.** For a state of the Savitch machine, the coordinate at index $14$ in its 18-entry register vector equals the value of its saved-endpoints stack register $SE$.

**Proof.** The saved-endpoints stack register $SE$ appears at index $14$ in the ordered register vector. Thus the coordinate selected by $r_{SE}$ is exactly $SE$.
