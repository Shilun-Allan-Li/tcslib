<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/PolyTimeBlockLoop.lean :: Complexity.polyTimeComputable_not -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Negation preserves polynomial-time computability

**Claim.** If the one-bit output function for a Boolean predicate $p$ is polynomial-time computable, then so is the one-bit output function for its negation.

**Proof.** Apply polynomial-time closure under a Boolean conditional to the predicate $p$, choosing the constant one-bit word $[\mathrm{false}]$ in the true case and $[\mathrm{true}]$ in the false case. The resulting output is $[\neg p(x)]$, as is seen by considering the two possible Boolean values of $p(x)$. The constant branches are polynomial-time computable, so the conditional construction proves the claim.

**Key facts.** `Complexity.polyTimeComputable_const`, `Complexity.polyTimeComputable_ite`.
