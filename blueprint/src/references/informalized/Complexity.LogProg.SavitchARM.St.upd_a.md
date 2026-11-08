<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/SavitchARM/Machine.lean :: Complexity.LogProg.SavitchARM.St.upd_a -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating the base register

**Claim.** Replacing coordinate $1$ of the register vector by $k$ gives the register vector of the state obtained from $st$ by setting its base register to $k$.

**Proof.** Both sides are functions from the 18 coordinates to natural numbers. Since $r_a=1$ and the base register occupies coordinate $1$ in the vector, the two functions agree at every coordinate: there they both have value $k$, and at every other coordinate they retain the corresponding original register value. Function extensionality therefore gives the claimed equality.
