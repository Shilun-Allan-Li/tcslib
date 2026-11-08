<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/SavitchARM/Machine.lean :: Complexity.LogProg.SavitchARM.St.upd_n -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating the input-length counter

**Claim.** Replacing coordinate $0$ of the register vector by $k$ gives the register vector of the state obtained from $st$ by setting its input-length counter to $k$.

**Proof.** Both sides are functions from the 18 coordinates to natural numbers. Since $r_n=0$ and the input-length counter occupies coordinate $0$ in the vector, the two functions agree at every coordinate: there they both have value $k$, and at every other coordinate they retain the corresponding original register value. Function extensionality therefore gives the claimed equality.
