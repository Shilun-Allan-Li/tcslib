<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/SavitchARM/Machine.lean :: Complexity.LogProg.SavitchARM.St.toV_T -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Scratch register coordinate

**Claim.** For a state of the Savitch machine, the coordinate at index $4$ in its 18-entry register vector equals the value of its scratch register $T$.

**Proof.** The scratch register $T$ occurs at index $4$ in the ordered register vector. Therefore, selecting the coordinate indexed by $r_T$ returns $T$.
