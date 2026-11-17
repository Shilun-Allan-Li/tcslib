<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/FormulaKit/Emit.lean :: Complexity.FormulaKit.polyTimeComputable_unary_add -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Unary Addition

**Claim.** If the unary strings for $f(x)$ and $g(x)$ are polynomial-time computable, then so is the unary string for $f(x)+g(x)$.

**Proof.** Compute the two unary strings and concatenate them; closure of polynomial-time computable functions under concatenation gives a polynomial-time computation (`PolyTimeComputable.append`). The concatenation of $f(x)$ ones and $g(x)$ ones is exactly the string of $f(x)+g(x)$ ones, by the addition rule for list replication.

**Key facts.** `Complexity.PolyTimeComputable.append`.
