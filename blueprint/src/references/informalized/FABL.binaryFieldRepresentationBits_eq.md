<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/ExecutableFiniteFields.lean :: FABL.binaryFieldRepresentationBits_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binary Field Representation Bit Count

**Claim.** For every natural number $\ell$, the number of bits in the binary field representation equals $\ell\bigl(1+2^\ell+6\cdot 2^{2\ell}\bigr)$.

**Proof.** The bit count is $\ell$ times one plus the number of binary vectors of length $\ell$ plus six times the number of ordered pairs of such vectors. There are $2^\ell$ binary vectors (`length_allBinaryVectors`) and $2^{2\ell}$ ordered pairs (`length_binaryVectorPairs`). Substituting these two counts into the definition gives the formula.

**Key facts.** `FABL.length_allBinaryVectors`, `FABL.length_binaryVectorPairs`.
