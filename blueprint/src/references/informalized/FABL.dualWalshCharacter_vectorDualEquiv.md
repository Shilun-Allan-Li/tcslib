<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LearningTheory/SparseSpectrum.lean :: FABL.dualWalshCharacter_vectorDualEquiv -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Identification of vector and dual characters

**Claim.** Under the standard dot-product identification of $\mathbb{F}_2^n$ with its dual, the dual Walsh character indexed by $\gamma$ equals the vector Walsh character indexed by $\gamma$.

**Proof.** Evaluate both characters at an arbitrary vector $x$. The dual character evaluates to the binary sign of the functional's value at $x$ (`FABL.dualWalshCharacter_apply`). Under the standard identification, that value is the dot product of $\gamma$ and $x$ (`FABL.vectorDualEquiv_apply`). The vector Walsh character is also the binary sign of this dot product (`FABL.vectorWalshCharacter_apply`). Hence the characters agree at every $x$, and therefore are equal.

**Key facts.** `FABL.dualWalshCharacter_apply`, `FABL.vectorDualEquiv_apply`, `FABL.vectorWalshCharacter_apply`.
