<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.a3n_poly_fixed_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Equality with a Fixed Word

**Claim.** For every fixed binary word $w$, the function mapping $x$ to the one-bit word recording whether $x=w$ is polynomial-time computable.

**Proof.** A machine can test whether its input equals the fixed word $w$ and output $[\text{true}]$ on equality and $[\text{false}]$ otherwise, within a linear time bound (Turing.FinTM.computesFunInTime_ifEq). Linear-time computability implies polynomial-time computability (Complexity.a3n_poly_linear). The resulting conditional output is exactly the one-bit word recording whether $x=w$, as is seen by considering the cases $x=w$ and $x\ne w$.

**Key facts.** `Turing.FinTM.computesFunInTime_ifEq`, `Complexity.a3n_poly_linear`.
