<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/ISCountRegs.lean :: Complexity.LogProg.ISCount.St.upd_s -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating the window radius

**Claim.** Replacing coordinate 3 of the register vector of a state by $z$ gives the register vector of the state whose window-radius register is $z$.

**Proof.** It is enough to check the vectors coordinate by coordinate. At coordinate $3$, the update replaces the window-radius entry by $z$, matching the modified state. At each other coordinate, both vectors retain the original register value. Therefore they are equal.
