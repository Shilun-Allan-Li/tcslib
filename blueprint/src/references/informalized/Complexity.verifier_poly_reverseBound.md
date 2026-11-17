<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/NP.lean :: Complexity.verifier_poly_reverseBound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-time reverse length comparison

**Claim.** For all $C,c\in\mathbb{N}$, the function that outputs $1$ exactly when $C(|\pi_1(z)|+1)^c\le |\pi_2(z)|$ is polynomial-time computable, with invalid pair encodings interpreted as having empty components.

**Proof.** First compute the decoded first and second components, using polynomial-time algorithms for the two default projections (\texttt{Complexity.polyTimeComputable_pairFstD} and \texttt{Complexity.polyTimeComputable_pairSndD}). For an input list $x$, a polynomial-time machine can produce a string of $C(|x|+1)^c$ ones (\texttt{Turing.FinTM.computesFunInTime_polyUnary}); prepending one further $1$ is also polynomial-time computable (\texttt{Turing.FinTM.computesFunInTime_prepend}). This gives, from the first component, a unary string whose length is $C(|a|+1)^c+1$. Pair that string with the decoded second component, using polynomial-time composition and pair encoding (\texttt{Complexity.PolyTimeComputable.comp} and \texttt{Complexity.PolyTimeComputable.pairEncode}). Apply the polynomial-time bound test with parameters $1,1$ (\texttt{Complexity.verifier_poly_bound}). On a valid encoded pair, its condition is $|b|\le |1^{C(|a|+1)^c+1}|+1$, equivalently $C(|a|+1)^c\le |b|$. The decoding identity for pair encoding verifies that these are the components tested (\texttt{Turing.pairDecode_pairEncode}). If the original input does not decode, the default projections are empty, and the same construction still computes the specified comparison for those empty components.

**Key facts.** `Complexity.polyTimeComputable_pairFstD`, `Complexity.polyTimeComputable_pairSndD`, `Turing.FinTM.computesFunInTime_polyUnary`, `Turing.FinTM.computesFunInTime_prepend`, `Complexity.polyTimeComputable_of_linear`, `Complexity.PolyTimeComputable.comp`, `Complexity.PolyTimeComputable.pairEncode`, `Complexity.verifier_poly_bound`, `Turing.pairDecode_pairEncode`.
