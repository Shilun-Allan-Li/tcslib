<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/KushilevitzMansour.lean :: FABL.isFourierSpectrumConcentratedOn_of_goldreichLevin_complete -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Goldreich–Levin Spectrum Completion

**Claim.** Given the hypotheses in the statement, the squared Fourier weight of a Boolean function outside the output family is at most $\epsilon/2$.

**Proof.** Let the sets outside the output family be divided into those already outside the initial family and those in the initial family but missed by the output family. These two collections are disjoint, and together contain every set outside the output family. The initial outside collection has squared Fourier weight at most $\epsilon/4$ by hypothesis.

For a missed set in the initial family, completeness of the output family implies that its coefficient magnitude is strictly below the Goldreich–Levin threshold: otherwise completeness would place it in the output family. Its squared coefficient is therefore at most the square of that threshold. There are at most $M$ missed sets, so their total squared weight is at most $M$ times the squared threshold. Using the threshold $\epsilon/(4M)$ and $0<\epsilon<1/2$, this is at most $\epsilon/4$. Adding the two disjoint contributions gives the bound $\epsilon/2$. The parameter bounds used here follow from the fact that a positive learning parameter, viewed as a real number, lies in $(0,1/2)$.

**Key facts.** `FABL.positiveLearningParameter_toReal_mem_Ioc`.
