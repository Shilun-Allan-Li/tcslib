<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/ExecutableFiniteFields.lean :: FABL.binaryVectorEnumerationEquiv_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Value of the Vector Enumeration

**Claim.** For every $\ell$ and every index $i<2^\ell$, the binary vector enumeration equivalence sends $i$ to the entry of the recursively defined list at the corresponding index under the canonical length identification.

**Proof.** The enumeration equivalence is the composite of the canonical identification from indices below $2^\ell$ to indices below the list length and the list equivalence that returns the entry at an index. Applying this composite to $i$ therefore gives exactly the list entry at the transported index. This is the defining evaluation rule for the list equivalence.

**Key facts.** `FABL.length_allBinaryVectors`.
