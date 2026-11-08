<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/ExecutableFiniteFields.lean :: FABL.binaryFieldPreprocessingWork_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binary Field Preprocessing Work Bound

**Claim.** For every natural number $\ell$, the binary field preprocessing work is at most $2^{8(\ell+1)}$.

**Proof.** Set $C=(\ell+1)^2 2^{3\ell}$. First bound each component of the preprocessing work by a multiple of $C$. The vector-enumeration estimate, together with $\ell+1\le(\ell+1)^2$ and $2^\ell\le2^{3\ell}$, gives at most $4C$ (`binaryVectorEnumerationWork_le`). The modulus-search estimate already gives at most $9C$ (`binaryModulusSearchWork_le`). The addition-table, multiplication-table, and representation-bit estimates give at most $C$, $9C$, and $8C$, respectively: use their stated bounds and $2^{2\ell}\le2^{3\ell}$ (`binaryAdditionTableWork_le`, `binaryMultiplicationTableWork_le`, and `binaryFieldRepresentationBits_le`). Summing these five estimates bounds total preprocessing work by $31C$, hence by $32C. Next, $\ell+1\le2^{\ell+1}$ (`nat_succ_le_two_pow_succ`), so $32(\ell+1)^2 2^{3\ell}\le32(2^{\ell+1})^2 2^{3\ell}$. Writing $32=2^5$ and combining powers of $2$ makes the latter $2^{5+2(\ell+1)+3\ell}$. The exponent is at most $8(\ell+1)$, proving the claimed bound.

**Key facts.** `FABL.binaryVectorEnumerationWork_le`, `FABL.binaryModulusSearchWork_le`, `FABL.binaryAdditionTableWork_le`, `FABL.binaryMultiplicationTableWork_le`, `FABL.binaryFieldRepresentationBits_le`, `FABL.nat_succ_le_two_pow_succ`.
