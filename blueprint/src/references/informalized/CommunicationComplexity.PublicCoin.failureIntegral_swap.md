<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/Minimax.lean :: CommunicationComplexity.PublicCoin.failureIntegral_swap -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Swapping Failure-Probability Averages

**Claim.** The average over coin tapes of the input-distribution probability of failure equals the average over inputs of the coin-tape probability of failure.

**Proof.** For each fixed coin tape, express the probability of the failure set in $X\times Y$ as the integral of its indicator function (`measureReal_eq_integral_indicator_one`). Likewise, for each fixed input pair, express the probability of failure over coin tapes as the integral of the corresponding indicator. Substituting these identities turns both sides into iterated integrals of the same failure indicator. The integrand is integrable because it is bounded and the spaces are finite; Fubini’s theorem therefore permits exchanging the order of integration. This gives the claimed equality.

**Key facts.** `CommunicationComplexity.FiniteProbabilitySpace.measureReal_eq_integral_indicator_one`.
