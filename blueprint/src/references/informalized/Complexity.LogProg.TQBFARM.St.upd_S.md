<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFARM/Machine.lean :: Complexity.LogProg.TQBFARM.St.upd_S -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating the Assignment Stack

**Claim.** Updating register 1 of the register vector for a state $s$ to $k$ gives the register vector of the state obtained by setting $S=k$.

**Proof.** To prove equality of the two register vectors, compare their values at an arbitrary coordinate $r\in\mathrm{Fin}(7)$. The register vector lists the seven fields in order. If $r=1$, both sides have value $k$; at each of the other six coordinates, the update leaves the original value unchanged, and the state update leaves the corresponding field unchanged. Thus the vectors agree at every coordinate.
