<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZeroPRun.lean :: Randomized.PIT.polyTimeComputable_restW -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Rest Transformation

**Claim.** The function defined by the case distinction for the rest transformation is polynomial-time computable.

**Proof.** The transformation chooses between the middle word when the variable tag is present, the body when the constant-one tag is present, and the second rest transformation otherwise. The tag tests are polynomial-time computable (`Randomized.PIT.polyTimeComputable_isVarW` and `Randomized.PIT.polyTimeComputable_isOneW`), and each of the three possible output functions is polynomial-time computable (`Randomized.PIT.polyTimeComputable_midW`, `Randomized.PIT.polyTimeComputable_bodyW`, and `Randomized.PIT.polyTimeComputable_rest2W`). Applying the closure of polynomial-time computability under a Boolean-controlled case distinction twice (`Complexity.polyTimeComputable_ite`) proves the result.

**Key facts.** `Randomized.PIT.polyTimeComputable_isVarW`, `Randomized.PIT.polyTimeComputable_midW`, `Randomized.PIT.polyTimeComputable_isOneW`, `Randomized.PIT.polyTimeComputable_bodyW`, `Randomized.PIT.polyTimeComputable_rest2W`, `Complexity.polyTimeComputable_ite`.
