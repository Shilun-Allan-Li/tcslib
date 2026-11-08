<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/ExecutableFiniteFields.lean :: FABL.binaryMulModStateWork_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Multiplication State Work

**Claim.** For all natural numbers $\ell$ and $r$, the work assigned to the multiplication state after $r$ steps is $r(6\ell+2)$.

**Proof.** Induct on $r$. At zero steps the state work and the claimed expression are both zero. For the successor step, the recurrence adds the work of one scale-add operation, one multiplication-by-$X$-modulo operation, and one additional unit. These operation costs are $2\ell$ (`binaryScaleAddWork_eq`) and $4\ell+1$ (`binaryXMulModWork_eq`). By the induction hypothesis, the total is $r(6\ell+2)+2\ell+(4\ell+1)+1=(r+1)(6\ell+2)$, as required.

**Key facts.** `FABL.binaryScaleAddWork_eq`, `FABL.binaryXMulModWork_eq`.
