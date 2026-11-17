<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clA5_pt_and -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Conjunction of Polynomial-Time Tests

**Claim.** If the single-bit output functions $x\mapsto[p(x)]$ and $x\mapsto[q(x)]$ are polynomial-time computable, then so is $x\mapsto[p(x)\land q(x)]$.

**Proof.** Use the polynomial-time conditional construction (`clA5_pt_cond`) with predicate $p$, true branch $x\mapsto[q(x)]$, and false branch the constant word $[\mathrm{false}]$ (`clA5_pt_const`). Its output is $[q(x)]$ when $p(x)$ is true and $[\mathrm{false}]$ otherwise, which in either Boolean case is exactly $[p(x)\land q(x)]$.

**Key facts.** `Complexity.clA5_pt_cond`, `Complexity.clA5_pt_const`.
