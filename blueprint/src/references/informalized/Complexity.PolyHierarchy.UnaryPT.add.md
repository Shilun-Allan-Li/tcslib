<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/PolyHierarchy/Padding.lean :: Complexity.PolyHierarchy.UnaryPT.add -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Addition of Unary Polynomial-Time Functions

**Claim.** If the unary representations of two functions on finite binary strings are computable in polynomial time, then the unary representation of their sum is computable in polynomial time.

**Proof.** By hypothesis, the maps sending an input $y$ to the unary strings of lengths $\ell_1(y)$ and $\ell_2(y)$ are polynomial-time computable. Pair encoding these two outputs is still polynomial-time computable (\texttt{PolyTimeComputable.pairEncode}); applying the polynomial-time map that decodes a pair and concatenates its components preserves polynomial-time computability by composition (\texttt{PolyTimeComputable.comp}, \texttt{polyTimeComputable\_pairConcat}). The resulting string is the concatenation of the two unary strings, hence is unary of length $\ell_1(y)+\ell_2(y)$. This is the required representation.

**Key facts.** `Complexity.PolyTimeComputable.pairEncode`, `Complexity.polyTimeComputable_pairConcat`, `Complexity.PolyTimeComputable.comp`.
