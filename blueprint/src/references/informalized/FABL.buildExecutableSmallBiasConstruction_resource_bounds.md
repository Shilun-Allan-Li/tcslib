<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/SmallBiasAlgorithm.lean :: FABL.buildExecutableSmallBiasConstruction_resource_bounds -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Small-bias resource bounds

**Claim.** For $n\in\mathbb N$ and $\ell>0$, the constructed small-bias construction has $2^{2\ell}$ outputs. Its field representation size is at most its field preprocessing work, that work is at most $2^{8(\ell+1)}$, and total construction work is the preprocessing work plus $2^{2\ell}$ times one more than the row work.

**Proof.** Unfold the construction to identify its output list with the executable generator list built from the field model. The output-count result for that list gives length $2^{2\ell}$ (`length_executableSmallBiasGeneratorList`). The field representation bound follows from `binaryFieldRepresentationBits_le_preprocessingWork`, and the exponential upper bound on preprocessing work follows from `binaryFieldPreprocessingWork_le`. Finally, `executableSmallBiasConstructionWork_eq` gives the stated formula for total construction work.

**Key facts.** `FABL.length_executableSmallBiasGeneratorList`, `FABL.binaryFieldRepresentationBits_le_preprocessingWork`, `FABL.binaryFieldPreprocessingWork_le`, `FABL.executableSmallBiasConstructionWork_eq`.
