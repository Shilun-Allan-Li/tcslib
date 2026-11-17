<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/JuntaFourierGap.lean :: FABL.isRelevant_toReal_of_fourierCoeff_ne_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier Support Implies Relevance for Boolean Functions

**Claim.** For a Boolean function, if its real-valued Fourier coefficient at $S$ is nonzero, then every coordinate $i\in S$ is relevant.

**Proof.** Apply the result that any nonzero Fourier coefficient indexed by a set containing $i$ forces positive influence at $i$ (\texttt{FABL.isRelevant_of_fourierCoeff_ne_zero}) to the real-valued version of the Boolean function, using the given nonzero coefficient and $i\in S$.

**Key facts.** `FABL.isRelevant_of_fourierCoeff_ne_zero`.
