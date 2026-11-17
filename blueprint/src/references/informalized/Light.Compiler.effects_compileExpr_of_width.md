<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/Expressions.lean :: Light.Compiler.effects_compileExpr_of_width -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expression Effects from Width

**Claim.** For a framed memory, if an expression has width at most $F$, is safe, and $k\le F+1$, then its compiled code writes its value to temporary cell $k$ and leaves memory unchanged outside the permitted address and temporary cells.

**Proof.** The width bound is equivalent to the conjunction that the expression’s variable count and height are each at most $F$ (`Light.Expr.width_le_iff`). Use the variable-count bound and safety hypothesis in the compiled-expression theorem. The height bound, together with $k\le F+1$, implies $k+\mathrm{height}(e)\le 2F+1$, which is that theorem’s temporary-space requirement. It then gives both the value written at cell $k$ and the stated memory-preservation property (`Light.Compiler.effects_compileExpr`).

**Key facts.** `Light.Expr.width_le_iff`, `Light.Compiler.effects_compileExpr`.
