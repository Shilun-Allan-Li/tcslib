<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/ExecutableFiniteFields.lean :: FABL.binaryFieldRepresentationBits_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binary Field Representation Bit Bound

**Claim.** For every natural number $\ell$, the number of bits in the binary field representation is at most $8(\ell+1)^2 2^{2\ell}$.

**Proof.** Use the exact bit-count formula (`binaryFieldRepresentationBits_eq`). Since $2^\ell\le2^{2\ell}$ and $1\le2^{2\ell}$, its parenthesized factor satisfies $1+2^\ell+6\cdot2^{2\ell}\le8\cdot2^{2\ell}$. Also $\ell\le(\ell+1)^2$. Multiplying these nonnegative bounds gives $\ell(1+2^\ell+6\cdot2^{2\ell})\le8(\ell+1)^2 2^{2\ell}$, as required.

**Key facts.** `FABL.binaryFieldRepresentationBits_eq`.
