<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/OneWayMinimax.lean :: CommunicationComplexity.PublicCoin.OneWay.failureIntegral_swap -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Swapping Failure Integrals

**Claim.** The integral over coin tapes of the input-pair failure probability equals the integral over input pairs of the coin-tape failure probability.

**Proof.** For each fixed coin tape, the measure of the set of failing input pairs equals the integral over input pairs of the indicator of failure (`measureReal_eq_integral_indicator_one`). Likewise, for each fixed input pair, the measure of the failing coin tapes equals the integral over coin tapes of the corresponding indicator. Substituting these representations into the two sides reduces the claim to exchanging the order of integration for the indicator of the failure relation on the product of the two finite spaces. This indicator is integrable because the spaces are finite; Fubini's theorem therefore identifies the iterated integrals in either order. The resulting inner integrals are precisely the indicator representations of the two failure measures above.

**Key facts.** `CommunicationComplexity.FiniteProbabilitySpace.measureReal_eq_integral_indicator_one`.
