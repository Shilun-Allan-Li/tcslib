<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/SmallBiasFourierAlgorithm.lean :: FABL.SmallBiasFourierInput.sample_isBiased -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bias of the Sample Distribution

**Claim.** The sample distribution is biased with parameter equal to the input bias divided by the Fourier bound.

**Proof.** Let the generator input be the one obtained from the Fourier input, and apply the deterministic small-bias algorithm to it. The algorithm's specification supplies a biased generator density with parameter equal to the generator input's bias. The sample count's positivity ensures the finite sample space is nonempty, and the generator input has positive field degree, as required by the construction. The sample density is this generator density after reindexing the sample space by the equivalence that enumerates pairs of binary vectors of length equal to the field degree. A uniform pushforward remains biased with the same parameter under such an equivalence (`ProbabilityDensity.IsBiased.uniformPushforward_comp_equiv`). Finally, the generator input's bias equals the original input bias divided by the Fourier bound (`SmallBiasFourierInput.generatorInput_epsilon`), giving the claimed parameter.

**Key facts.** `FABL.SmallBiasFourierInput.sampleCount_pos`, `FABL.SmallBiasInput.fieldDegree_pos`, `FABL.deterministicSmallBiasAlgorithm_spec`, `FABL.ProbabilityDensity.IsBiased.uniformPushforward_comp_equiv`, `FABL.SmallBiasFourierInput.generatorInput_epsilon`.
