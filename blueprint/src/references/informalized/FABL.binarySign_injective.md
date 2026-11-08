<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LearningTheory/SparseSpectrum.lean :: FABL.binarySign_injective -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Injectivity of the Binary Sign

**Claim.** The binary sign map from $\mathbb{F}_2$ to $\mathbb{R}$ is injective.

**Proof.** Suppose two elements have the same binary sign. If the first is zero, its sign is one, so the second also has sign one and must be zero by the characterization of when the binary sign equals one (`FABL.binarySign_eq_one_iff`). If the first is nonzero, it equals one. If the second were zero, equality of signs would force the first sign to be one, contradicting the same characterization; hence the second is also nonzero and therefore equals one. In either case the two elements agree.

**Key facts.** `FABL.binarySign_eq_one_iff`.
