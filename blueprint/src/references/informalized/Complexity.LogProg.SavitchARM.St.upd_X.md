<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/SavitchARM/Machine.lean :: Complexity.LogProg.SavitchARM.St.upd_X -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating the exponent counter

**Claim.** Replacing coordinate $2$ of the register vector by $k$ gives the register vector of the state obtained from $st$ by setting its exponent counter to $k$.

**Proof.** Both sides are functions from the 18 coordinates to natural numbers. Since $r_X=2$ and the exponent counter occupies coordinate $2$ in the vector, the two functions agree at every coordinate: there they both have value $k$, and at every other coordinate they retain the corresponding original register value. Function extensionality therefore gives the claimed equality.
