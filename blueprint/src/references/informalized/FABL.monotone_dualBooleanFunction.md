<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/KKLBribery.lean :: FABL.monotone_dualBooleanFunction -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of the Dual Function

**Claim.** If $f$ is monotone on the sign cube, then the dual function $x\mapsto -f(-x)$ is also monotone.

**Proof.** Let $x\le y$. Since signs take only the values $-1$ and $1$, coordinatewise comparison implies $-y\le -x$: this follows by checking the possible sign pairs, with the only forbidden pair for $x_i\le y_i$ being $x_i=1,y_i=-1$. Monotonicity of $f$ therefore gives $f(-y)\le f(-x)$. Negating this inequality reverses the order and yields $-f(-x)\le -f(-y)$, which is the required comparison of the dual function at $x$ and $y$. The sign order bounds, such as $-1\le s$ (`neg_one_le_sign`), support the coordinatewise sign checks.

**Key facts.** `FABL.neg_one_le_sign`.
