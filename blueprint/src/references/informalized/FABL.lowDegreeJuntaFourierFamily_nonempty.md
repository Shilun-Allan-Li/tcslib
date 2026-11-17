<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeJuntaLearning.lean :: FABL.lowDegreeJuntaFourierFamily_nonempty -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonempty Low-Degree Fourier Family

**Claim.** For natural numbers $n,k$ and a subset $P$ of the $n$-element index set, the family of subsets of indices outside $P$ of size at most $\lfloor3k/4\rfloor$ is nonempty.

**Proof.** The family for indices outside $P$ is defined as the low-degree Fourier family on the finite set of those indices, with cutoff $\lfloor3k/4\rfloor$. Apply the general nonemptiness theorem for a low-degree Fourier family (`lowDegreeFourierFamily_nonempty`) to that dimension and cutoff.

**Key facts.** `FABL.lowDegreeFourierFamily_nonempty`.
