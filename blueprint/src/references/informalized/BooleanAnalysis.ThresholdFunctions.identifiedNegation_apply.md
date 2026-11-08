<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/NoiseStability.lean :: BooleanAnalysis.ThresholdFunctions.identifiedNegation_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Negated identification as XOR

**Claim.** For every input $w$, negated coordinate identification evaluates $f$ at the coordinatewise XOR of $z$ with the identified coordinates of $w$.

**Proof.** Unfold the definitions of negated identification and coordinatewise XOR. The two resulting Boolean inputs to $f$ agree coordinate by coordinate: if $z_i$ is false, both give $w_{[0m\pi(i)}$; if $z_i$ is true, both give its Boolean negation. Thus the inputs, and hence their values under $f$, are equal.
