<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LearningTheory/LearningModel.lean :: FABL.finiteFamily_nonempty_of_spectrum_concentrated -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonempty family from Fourier concentration

**Claim.** If the Fourier weight outside the finite family is at most $\varepsilon/2$, then the family is nonempty.

**Proof.** Suppose instead that the family is empty. Its upward closure as a set of subsets is then the empty set, so the concentration hypothesis says that the Fourier spectrum is concentrated on the empty set with tolerance $\varepsilon/2$. But a Boolean function cannot have its Fourier weight outside the empty set at most this tolerance (`FABL.not_isFourierSpectrumConcentratedOn_empty`). This contradiction proves that the family is nonempty.

**Key facts.** `FABL.not_isFourierSpectrumConcentratedOn_empty`.
