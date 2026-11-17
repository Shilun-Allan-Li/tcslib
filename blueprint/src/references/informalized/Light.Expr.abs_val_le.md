<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/RunsStayInLimits.lean :: Light.Expr.abs_val_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bound on Safe Expression Values

**Claim.** If all location and memory values in a state have absolute value at most the word limit, then every expression safe in that state has value whose absolute value is at most the word limit.

**Proof.** Proceed by cases on the expression. A natural-number constant is nonnegative, so its absolute value is the constant itself, and safety bounds it by the word limit. A variable is bounded by the assumed bound on locations. For a binary operation, safety directly includes the required bound on the absolute value of its result. For a load, safety guarantees a valid address, and the assumed bound on memory values applies at that address.
