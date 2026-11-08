<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satSyntax_poly -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Syntax Testing

**Claim.** The function sending each bit string $x$ to the one-bit output containing the Boolean result of the complete CNF syntax test is polynomial-time computable.

**Proof.** Use the finite-state scan machine whose transition is the syntax-state update and whose acceptance bit tests whether the final state is $4$. The scan computation theorem (satScan_computes) says this machine outputs that acceptance bit after scanning $x$ and runs in time $|x|+1$. This is a polynomial bound, with both multiplicative constant and exponent equal to $1$.

**Key facts.** `Complexity.satScan_computes`.
