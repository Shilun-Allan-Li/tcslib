<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/SavitchARM/Machine.lean :: Complexity.LogProg.SavitchARM.St.upd_U -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating the source-code register

**Claim.** Replacing coordinate $10$ of the register vector by $k$ gives the register vector of the state obtained by setting its source-code register to $k$.

**Proof.** Both sides are functions from the 18 coordinates to natural numbers. Since $r_U=10$ and the source-code register occupies coordinate $10$ in the vector, the two functions agree at every coordinate: there they both have value $k$, and at every other coordinate they retain the corresponding original register value. Function extensionality therefore gives the claimed equality.
