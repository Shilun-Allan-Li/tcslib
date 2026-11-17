<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/DeterministicGoldreichLevin.lean :: FABL.DeterministicGoldreichLevinInput.threshold_cast -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Threshold as a real quotient

**Claim.** The threshold, viewed as a real number, equals the real learning parameter divided by four times the family-size bound.

**Proof.** By definition, the threshold is the rational learning parameter divided by the rational number four times the family-size bound. The rational-to-real map preserves division, multiplication, and the natural-number cast. Casting the defining quotient therefore gives the real learning parameter divided by four times the real family-size bound, as claimed.
