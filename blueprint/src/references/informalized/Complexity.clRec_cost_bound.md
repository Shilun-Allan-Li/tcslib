<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clRec_cost_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Quadratic Recording-Work Bound

**Claim.** For every finite Boolean Turing machine $M$ and every natural number $T$, if $F$ is the number of movement-count fields, then $(T+1)(F(3T+4)+2T+7)\le(4F+7)(T+1)^2$.

**Proof.** First, $3T+4\le 4(T+1)$, since the right side exceeds the left by $T$. Multiplying by $F$ and adding the remaining terms gives
\[
F(3T+4)+2T+7\le 4F(T+1)+7(T+1)=(4F+7)(T+1),
\]
where the final equality is an expansion. Multiplying this inequality by the nonnegative number $T+1$ preserves its direction. Expanding the resulting right-hand side yields the claimed bound.
