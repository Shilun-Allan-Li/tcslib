<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ImplicitPoly.lean :: Complexity.ImplicitlyLogspaceComputable.polyTimeComputable -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Implicit logspace implies polynomial-time computability

**Claim.** If $f$ has polynomially bounded output length and its output-bit and output-length index languages are in LOGSPACE, then $f$ is computable by a finite-state deterministic machine in polynomial time.

**Proof.** Apply the space construction for implicit logspace computation (`ImplicitlyLogspaceComputable.computesInSpace`) to obtain a machine computing $f$ with space bounded by a constant multiple of logarithmic input length. The conversion theorem `polyTimeComputable_of_computesInSpace` says that any such logarithmic-space computation of a function is also a polynomial-time computation. Applying it to the machine just obtained proves the claim.

**Key facts.** `Complexity.ImplicitlyLogspaceComputable.computesInSpace`, `Complexity.polyTimeComputable_of_computesInSpace`.
