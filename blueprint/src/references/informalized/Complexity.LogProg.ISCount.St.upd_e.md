<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/ISCountRegs.lean :: Complexity.LogProg.ISCount.St.upd_e -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating the code-bound exponent

**Claim.** Updating the vector of a state at register index $4$ to $z$ yields the vector of the state with code-bound exponent replaced by $z$.

**Proof.** Compare the two vectors at an arbitrary register index. At index $4$, the update and the replacement of the exponent both give $z$. At all remaining indices, the entries are unchanged from the corresponding registers of $\sigma$. Checking the 17 possibilities proves equality coordinate by coordinate.
