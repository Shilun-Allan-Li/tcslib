<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/FormulaKit/Emit.lean :: Complexity.FormulaKit.polyTimeComputable_unary_pow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Unary Powers

**Claim.** If the unary string for $f(x)$ is polynomial-time computable, then for each natural number $k$, the unary string for $f(x)^k$ is polynomial-time computable.

**Proof.** Induct on $k$. For $k=0$, the output is always the one-symbol string $[\mathrm{true}]$, so it is polynomial-time computable (`polyTimeComputable_const`). For the successor case, the induction hypothesis gives the unary string for $f(x)^k$, and the assumption gives the unary string for $f(x)$. The unary multiplication result combines these to compute the unary string for $f(x)^k f(x)=f(x)^{k+1}$ (`polyTimeComputable_unary_mul`).

**Key facts.** `Complexity.polyTimeComputable_const`, `Complexity.FormulaKit.polyTimeComputable_unary_mul`.
