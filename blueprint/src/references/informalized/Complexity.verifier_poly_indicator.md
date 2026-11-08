<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/NP.lean :: Complexity.verifier_poly_indicator -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-time language indicators

**Claim.** If a binary language $V$ belongs to $\mathsf{P}$, then its one-bit indicator function is polynomial-time computable.

**Proof.** By the characterization of $\mathsf{P}$, there are a machine $M$ and constants $C,c$ such that $M$ computes the one-bit indicator of $V$ in time $C(n+1)^c$ (\texttt{Complexity.mem_P_iff}). Thus the indicator predicate itself is polynomial-time computable. The two constant functions returning the one-bit strings $[1]$ and $[0]$ are also polynomial-time computable (\texttt{Complexity.polyTimeComputable_const}). Combining these functions by a conditional on the indicator predicate yields the function that returns $[1]$ for members of $V$ and $[0]$ otherwise (\texttt{Complexity.polyTimeComputable_ite}). This conditional is exactly the required indicator function.

**Key facts.** `Complexity.mem_P_iff`, `Complexity.polyTimeComputable_const`, `Complexity.polyTimeComputable_ite`.
