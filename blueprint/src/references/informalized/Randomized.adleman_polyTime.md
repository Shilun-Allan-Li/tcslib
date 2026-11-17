<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/PolyTimeModel.lean :: Randomized.adleman_polyTime -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-time randomized to circuits

**Claim.** If $L$ has the stated polynomial-time randomized verifier with two-thirds acceptance on members and two-thirds rejection on nonmembers, then $L$ is decidable by a family of fan-in-two circuits of polynomial size.

**Proof.** Apply the general randomized-to-circuits theorem (`Randomized.adleman`) to the polynomial-time verifier model. Its majority-closure hypothesis is supplied by `Randomized.polyTimeModel_closedUnderMajority`, and its circuit-simulation hypothesis by `Randomized.polyTimeModel_verifierHasCircuits`. These results establish precisely the two assumptions required by the general theorem, so its conclusion gives $L\in\mathrm{PPoly}$, which is the asserted polynomial-size fan-in-two circuit family.

**Key facts.** `Randomized.adleman`, `Randomized.polyTimeModel_closedUnderMajority`, `Randomized.polyTimeModel_verifierHasCircuits`.
