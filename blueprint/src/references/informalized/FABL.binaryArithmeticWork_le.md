<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/ExecutableFiniteFields.lean :: FABL.binaryArithmeticWork_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Explicit Arithmetic Work Bound

**Claim.** For every natural number $\ell$, the binary arithmetic work is at most $8(\ell+1)^2$.

**Proof.** The total work is the maximum of the addition work and the modular multiplication work. The addition work equals $\ell$, while the modular multiplication work equals $\ell(6\ell+2)$ (`binaryAddWork_eq`, `binaryMulModWork_eq`). It therefore suffices to bound each of these two expressions by $8(\ell+1)^2$. The addition bound follows immediately from $\ell\le 8(\ell+1)^2$; for the second, expanding gives $6\ell^2+2\ell\le 8(\ell+1)^2$, since the difference is $2\ell^2+14\ell+8\ge0$.

**Key facts.** `FABL.binaryAddWork_eq`, `FABL.binaryMulModWork_eq`.
