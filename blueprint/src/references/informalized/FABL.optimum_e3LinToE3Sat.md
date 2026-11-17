<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CSPAlgorithms.lean :: FABL.optimum_e3LinToE3Sat -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Optimum Under E3-Lin Reduction

**Claim.** For a finite-variable E3-Lin instance $P$, the optimum value of its four-clause E3-Sat reduction is $3/4+P.\mathrm{optimum}/4$.

**Proof.** For the upper bound, choose an assignment attaining the reduced instance's optimum. Its value is $3/4$ plus one quarter of the value of the corresponding E3-Lin assignment (`value_e3LinToE3Sat`); that original assignment's value is at most $P$'s optimum (`value_le_optimum`). Thus the reduced optimum is at most $3/4+P.\mathrm{optimum}/4$. For the reverse inequality, choose an assignment attaining $P$'s optimum (`exists_value_eq_optimum`) and convert it to a Boolean assignment. The conversion back to $\mathbb F_2$ recovers the chosen assignment (`boolAssignmentToF₂_f₂AssignmentToBool`), so the value formula identifies the reduced instance's value there as exactly $3/4+P.\mathrm{optimum}/4$. Every assignment's value is at most the reduced optimum (`value_le_optimum`), proving the reverse bound and hence equality.

**Key facts.** `FABL.CSPInstance.exists_value_eq_optimum`, `FABL.CSPInstance.value_le_optimum`, `FABL.value_e3LinToE3Sat`, `FABL.CSPInstance.exists_value_eq_optimum`, `FABL.boolAssignmentToF₂_f₂AssignmentToBool`, `FABL.value_e3LinToE3Sat`, `FABL.CSPInstance.value_le_optimum`.

**Caveat.** The supplied informal statement describes an approximation implication, but the formal statement and proof establish the exact optimum-value identity given in the claim.
