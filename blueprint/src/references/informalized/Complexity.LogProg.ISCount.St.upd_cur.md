<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/ISCountRegs.lean :: Complexity.LogProg.ISCount.St.upd_cur -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating the current walk code

**Claim.** Updating the vector of a state at register index $15$ to $z$ yields the vector of the state with current walk code replaced by $z$.

**Proof.** Compare the two register vectors at an arbitrary index and check the 17 possibilities. At index $15$, both vectors have value $z$; at every other index, both have the corresponding unchanged register of $\sigma$. Therefore the vectors are equal.
