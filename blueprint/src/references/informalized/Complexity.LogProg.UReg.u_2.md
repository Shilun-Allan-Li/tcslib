<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/UPathMachine.lean :: Complexity.LogProg.UReg.u_2 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating Register 2

**Claim.** For a register state with value vector $v$, replacing register $2$ by $z$ gives the same vector as updating coordinate $2$ of $v$ to $z$.

**Proof.** To prove equality of the two vectors, compare their values at each register coordinate. At coordinate $2$, the updated vector has value $z$, matching the record after register $2$ is replaced. At every other coordinate, both retain the original register value. Hence the vectors are equal.
