<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/KKLCounterexample.lean :: FABL.truncatedNormalizedRademacherSum_neg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sign Symmetry of the Truncated Sum

**Claim.** For every dimension and sign vector, evaluating the truncated normalized Rademacher sum at the coordinatewise negation gives the negative of its value at the original vector.

**Proof.** The normalized Rademacher sum changes sign when every coordinate is negated (the sign-change identity, `normalizedRademacherSum_neg`). Applying this identity to the sum inside the truncation reduces the claim to the oddness of projection onto $[-1,1]$ (`truncateUnit_neg`).

**Key facts.** `FABL.normalizedRademacherSum_neg`, `FABL.truncateUnit_neg`.
