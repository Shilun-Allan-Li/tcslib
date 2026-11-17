<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LearningTheory/SparseSpectrum.lean :: FABL.expect_dualWalshCharacter -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Average of a Dual Walsh Character

**Claim.** The uniform average of the dual Walsh character associated to $\psi$ is $1$ if $\psi=0$ and $0$ otherwise.

**Proof.** If $\psi=0$, its associated character is identically one, so its average is one. Otherwise, injectivity of the map from dual vectors to their associated characters (\texttt{dualWalshCharacter\_injective}) implies that the associated character is nontrivial. The character orthogonality formula for a finite group says that the average of a nontrivial character is zero, while that of the trivial character is one. Applying this formula yields the asserted case distinction.

**Key facts.** `FABL.dualWalshCharacter_injective`.
