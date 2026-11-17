<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/SmallBiasFourierAlgorithm.lean :: FABL.SmallBiasFourierInput.generatorInput_epsilon -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Generator bias scaling

**Claim.** The bias parameter of the associated generator input equals the target bias divided by the Fourier bound.

**Proof.** Write the target bias as its numerator divided by its denominator. The generator input retains the numerator and replaces the denominator by the original denominator multiplied by the Fourier bound. Both denominators are nonzero: the Fourier bound is at least one, and the target denominator is positive because it is at least twice the positive numerator. Hence ordinary fraction arithmetic gives the generator bias as the original bias divided by the Fourier bound.
