<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/ISCountRegs.lean :: Complexity.LogProg.ISCount.St.upd_cnt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating the inner count

**Claim.** Updating the vector of a state at register index $13$ to $z$ yields the vector of the state with inner count replaced by $z$.

**Proof.** To prove equality of the two register vectors, compare them at an arbitrary index. Since the index ranges over the 17 registers, checking each possible index reduces to the defining entries of the vector and of the update operation. At index $13$, both sides contain $z$; at every other index, both retain the corresponding register of $\sigma$. Thus the vectors agree at every coordinate.
