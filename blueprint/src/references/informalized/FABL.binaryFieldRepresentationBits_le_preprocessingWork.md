<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/ExecutableFiniteFields.lean :: FABL.binaryFieldRepresentationBits_le_preprocessingWork -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Representation bits are included in preprocessing work

**Claim.** For every natural number $\ell$, the number of bits in the binary field representation is at most the total binary field preprocessing work.

**Proof.** By definition, the total preprocessing work is a sum of five nonnegative natural numbers, one of which is the binary field representation bit count itself. Hence it is at least that summand.
