<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Switching.lean :: FABL.CoordRestriction.fixCoordinate_apply_of_ne -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Other Coordinates Remain Unchanged

**Claim.** Fixing coordinate $i$ according to a sign $s$ leaves the state at any distinct coordinate $j$ equal to its original value $\rho_j$.

**Proof.** A coordinate update replaces the value only at its target coordinate $i$. Since $j\ne i$, evaluation of the updated assignment at $j$ returns the original value $\rho_j$.
