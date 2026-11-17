<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.sat_pt_const -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Constant Word

**Claim.** For every fixed binary word $w$, the function sending every binary string to $w$ is polynomial-time computable.

**Proof.** The constant-word closure result supplies a polynomial-time computation that returns the fixed word $w$ on every input. This is exactly the function in question.

**Key facts.** `Complexity.polyTimeComputable_const`.
