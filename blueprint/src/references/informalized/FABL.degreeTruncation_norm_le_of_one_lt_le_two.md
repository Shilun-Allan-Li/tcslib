<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/HypercontractivityExercises.lean :: FABL.degreeTruncation_norm_le_of_one_lt_le_two -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Low-degree truncation norm bound

**Claim.** For $1<q\le2$, the uniform $L^q$ norm of the degree-$k$ Fourier truncation is at most $(1/\sqrt{q-1})^k$ times the uniform $L^q$ norm of the original function.

**Proof.** Set $r=q/(q-1)$, the Hölder conjugate exponent to $q$. The assumptions imply $r\ge2$. The bound for exponents at least two gives, for every function $g$, that truncation is bounded on uniform $L^r$ with factor $\sqrt{r-1}^{\,k}$ (`degreeTruncation_norm_le_of_two_le`). The truncation operator is self-adjoint (`degreeTruncation_selfAdjoint`), so the self-adjoint duality bound transfers this estimate to its action on uniform $L^q$ (`selfAdjoint_dual_bound`), with the same factor. Finally, $r-1=1/(q-1)$, and therefore $\sqrt{r-1}=1/\sqrt{q-1}$. Substitution gives the stated inequality.

**Key facts.** `FABL.degreeTruncation_norm_le_of_two_le`, `FABL.degreeTruncation_selfAdjoint`, `FABL.selfAdjoint_dual_bound`.
