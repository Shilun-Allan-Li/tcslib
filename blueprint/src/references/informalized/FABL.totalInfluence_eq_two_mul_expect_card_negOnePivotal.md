<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/DNFFormulas.lean :: FABL.totalInfluence_eq_two_mul_expect_card_negOnePivotal -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Total influence and negative pivotal coordinates

**Claim.** The total influence of a Boolean function equals twice the expected number of negative pivotal coordinates, where a coordinate is counted when the function is $-1$ and flipping it changes the function's value.

**Proof.** Replace each real-valued influence by the corresponding Boolean influence (FABL.booleanInfluence_eq_influence_toReal), then use the pivotal-coordinate identity: each Boolean influence is twice the uniform probability that the input has value $-1$ and the coordinate is pivotal (FABL.booleanInfluence_eq_two_mul_negOnePivotal_probability). Summing over coordinates and moving the finite sum inside the uniform expectation expresses the result as twice the expected sum of the indicators of these events. That sum counts precisely the negative pivotal coordinates, proving the formula.

**Key facts.** `FABL.booleanInfluence_eq_influence_toReal`, `FABL.booleanInfluence_eq_two_mul_negOnePivotal_probability`.
