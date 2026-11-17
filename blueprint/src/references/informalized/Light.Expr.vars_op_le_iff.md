<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/StatementCode.lean :: Light.Expr.vars_op_le_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Variable Bound for a Binary Operation

**Claim.** For any operation symbol $o$ and expressions $a,b$, the variable bound of the expression formed by applying $o$ to $a,b$ is at most $F$ exactly when the variable bounds of both $a$ and $b$ are at most $F$.

**Proof.** The variable bound of the operation expression is the maximum of the variable bounds of its two arguments. A maximum is at most $F$ if and only if each of its entries is at most $F$.
