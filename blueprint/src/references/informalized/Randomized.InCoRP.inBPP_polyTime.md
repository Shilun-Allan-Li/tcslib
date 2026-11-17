<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Inclusions.lean :: Randomized.InCoRP.inBPP_polyTime -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-time coRP is contained in BPP

**Claim.** Every language in polynomial-time coRP has a polynomial-time randomized verifier with acceptance and rejection probabilities each at least $2/3$ on members and nonmembers, respectively.

**Proof.** Apply the general implication from coRP to BPP, using the fact that the polynomial-time verifier model is closed under Boolean negation (Randomized.polyTimeModel_closedUnderNot). That implication gives the BPP verifier in the same model (Randomized.InCoRP.inBPP), which is precisely the stated polynomial-time conclusion.

**Key facts.** `Randomized.polyTimeModel_closedUnderNot`, `Randomized.InCoRP.inBPP`.
