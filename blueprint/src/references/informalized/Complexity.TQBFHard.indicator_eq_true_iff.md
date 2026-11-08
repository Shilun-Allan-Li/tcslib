<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFHardBridge.lean :: Complexity.TQBFHard.indicator_eq_true_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Indicator Membership Criterion

**Claim.** The Boolean indicator of a language is true at a bit string exactly when that string belongs to the language.

**Proof.** The indicator is defined to return true when the string belongs to the language and false otherwise. In the membership case its value equals true; in the nonmembership case its value is false. These two cases establish both directions of the equivalence.
