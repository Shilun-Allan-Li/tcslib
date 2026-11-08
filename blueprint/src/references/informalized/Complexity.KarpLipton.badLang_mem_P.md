<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/KarpLipton.lean :: Complexity.KarpLipton.badLang_mem_P -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# The bad-specification language is in polynomial time

**Claim.** For $V\in P$, the language of strings whose decoded components satisfy the bad-specification length bounds and at least one of the three stated bad cases is also in $P$.

**Proof.** Each decoded component $x,U,u,j,p$ can be computed in polynomial time. The marker-deleted circuit description is polynomial-time computable as well, and the pair of decoded strings used as a query can be formed in polynomial time by composing and pairing these functions. The various candidate suffixes are also polynomial-time computable: they are formed by unary strings of the required lengths, fixed marker bits, and the component strings. The unary length functions are polynomial-time computable by `unaryPT_poly` and the unary-string construction results; append and composition preserve polynomial-time computability.

Consequently, `pred_len_eq` and `pred_len_le` place each length test in $P$, while `pred_query` places every circuit-query acceptance test in $P$. For the leaf condition involving membership in $V$, the encoded pair is a polynomial-time function of the input, so `preimage_mem_P` puts that membership test in $P$; `pred_not` gives its complement. Closure of $P$ under conjunction, disjunction, and negation (`pred_and`, `pred_or`, and `pred_not`) then assembles the three bad cases together with their length bounds. This is exactly the decoded predicate defining the bad-specification language, so that language belongs to $P$.

**Key facts.** `Complexity.KarpLipton.polyTimeComputable_gx`, `Complexity.KarpLipton.polyTimeComputable_gu`, `Complexity.KarpLipton.polyTimeComputable_gj`, `Complexity.KarpLipton.polyTimeComputable_gp`, `Complexity.KarpLipton.polyTimeComputable_gU`, `Complexity.KarpLipton.polyTimeComputable_dropMarker`, `Complexity.PolyTimeComputable.pairEncode`, `Complexity.PolyHierarchy.unaryPT_poly`, `Complexity.PolyTimeComputable.append`, `Complexity.polyTimeComputable_const`, `Complexity.polyTimeComputable_prepend`, `Complexity.polyTimeComputable_unary`, `Complexity.KarpLipton.pred_len_eq`, `Complexity.KarpLipton.pred_len_le`, `Complexity.KarpLipton.pred_query`, `Complexity.preimage_mem_P`, `Complexity.KarpLipton.pred_not`, `Complexity.KarpLipton.pred_and`, `Complexity.KarpLipton.pred_or`.
