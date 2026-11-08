<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/VectorFourier.lean :: FABL.vectorWalshCharacter_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Walsh Character at the Zero Index

**Claim.** The Walsh character indexed by the zero vector is the constant character with value $1$.

**Proof.** Evaluate the zero-index character at an arbitrary vector using the evaluation formula (`vectorWalshCharacter_apply`). The dot product with the zero vector is zero, and the binary sign takes the value $1$ at zero. Thus the character agrees everywhere with the constant character; equality of characters follows from their pointwise equality.

**Key facts.** `FABL.vectorWalshCharacter_apply`.
