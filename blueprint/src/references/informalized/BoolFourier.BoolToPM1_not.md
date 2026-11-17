<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/BLR/BoolFourier.lean :: BoolFourier.BoolToPM1_not -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Negation under the sign embedding

**Claim.** For every Boolean value $b$, negating $b$ flips the sign of its image under the Bool-to-$\pm1$ embedding: $\mathrm{BoolToPM1}(\lnot b)=-\mathrm{BoolToPM1}(b)$.

**Proof.** The embedding is an abbreviation for the Boolean sign map. The sign map's negation identity, which says that complementing a Boolean value negates its sign, therefore gives the stated equation directly (`BooleanAnalysis.boolToSign_not`).

**Key facts.** `BooleanAnalysis.boolToSign_not`.
