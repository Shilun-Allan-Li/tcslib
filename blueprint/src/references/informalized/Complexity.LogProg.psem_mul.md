<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/UPathLoops.lean :: Complexity.LogProg.psem_mul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Register Multiplication Preserves Semantics

**Claim.** The specified nested register loops multiply the value of register $b$ by the initial difference $v(a)-v(i)$, add that product to register $R$, and preserve the given probabilistic semantics at the exit state.

**Proof.** Write $c=v(a)-v(i)$, which is nonnegative by hypothesis, and induct on $c$, generalizing the valuation. When $c=0$, the two compared registers are equal. The exit hypothesis at $z=v(j)$ simplifies to the semantics of the exit configuration with the original valuation, so the positive equality branch at $mo$ proves the claim.

For the successor case, $v(i)<v(a)$. First, the outer loop takes its unequal branch and clears $j$, giving a bounded valuation $v_1$. The inner loop then performs one complete pass: starting with $j=0$, it increments $R$ and $j$ together until $j=b$. Thus $R$ increases by $v(b)$, while $j$ ends at $v(b)$. The one-pass addition result (`psem_addOnce`) formalizes this inner loop; its register inequalities and bounds follow from the stated distinctness assumptions, the original bounds, and the bound on the final product.

Next, the outer loop increments $i$ once and returns to $mo$. The resulting valuation has $i$ increased by one, while $a$, $b$, and $R$ are unchanged except that $R$ has gained $v(b)$. Consequently the remaining difference between $a$ and $i$ is $c$, and the target value of $R$ is the original target: $v(R)+(c+1)v(b)=v(R)+cv(b)+v(b)$. The exit hypotheses for every bounded value of $j$ therefore supply exactly the induction hypotheses for this new valuation. The induction hypothesis gives semantics from the returned outer-loop state. Finally, the increment principle (`PSem.inc`), the clear-register principle (`PSem.clr`), and the unequal equality branch (`PSem.jeq_neg`) trace this semantics backward through the outer increment, initial clear, and initial comparison.

**Key facts.** `Complexity.LogProg.PSem.inc`, `Complexity.LogProg.PSem.clr`, `Complexity.LogProg.PSem.jeq_neg`, `Complexity.LogProg.psem_addOnce`, `Complexity.LogProg.register_update_le`.
