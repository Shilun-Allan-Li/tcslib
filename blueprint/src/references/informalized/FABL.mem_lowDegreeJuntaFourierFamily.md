<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeJuntaLearning.lean :: FABL.mem_lowDegreeJuntaFourierFamily -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Low-degree junta family membership

**Claim.** A set $S$ belongs to the low-degree Fourier family for the restriction outside $P$ exactly when $|S|\le\lfloor 3k/4\rfloor$.

**Proof.** The low-degree junta family is defined to be the low-degree Fourier family in the restriction dimension, with degree cutoff $\lfloor 3k/4\rfloor$. Apply the membership characterization for the low-degree Fourier family ( `FABL.mem_lowDegreeFourierFamily` ) with that cutoff. It says exactly that membership is equivalent to $|S|\le\lfloor 3k/4\rfloor$.

**Key facts.** `FABL.mem_lowDegreeFourierFamily`.
