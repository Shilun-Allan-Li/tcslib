<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/Conditions.lean :: Light.Compiler.decides_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Compiled equality test

**Claim.** Under the stated framing, boundedness, code-location, width, and safety assumptions, the compiled equality test runs in at most its size, reaching the position after the test when the two expressions have equal values and the target otherwise, while preserving memory outside the scratch cells.

**Proof.** 1. The condition-width bound gives separate width bounds for $a$ and $b$, and safety supplies the hypotheses needed to bound their values (`Light.Cond.width_eq_le_iff`, `Light.Expr.abs_val_le`). Execute the two compiled expressions in sequence. They place $a$ and $b$ in temporary cells, use at most $|a|+|b|$ steps, and preserve memory outside the scratch region (`Light.Compiler.steps_pair`). The code-location lemma exposes the remaining equality-test instructions immediately afterward (`Light.Compiler.codeAt_after_pair`).

2. The first subtraction computes $D=a-b$. Its value is representable because both expression values satisfy the word bound (`Light.Compiler.inRange_sub`). The next instruction branches to $l$ when $D<0$, which is precisely when $a<b$ and hence when the values are unequal in this branch. If $D$ is not negative, execution continues; the second subtraction replaces $D$ by $-D$, and the final branch sends execution to $l$ exactly when $-D<0$, that is, when $D>0$. Thus the target is reached for either strict inequality, while equality falls through to the position after the test. Each subtraction and branch takes one step (`WordRAM.steps_sub`, `WordRAM.steps_bltz`), and composing these with expression evaluation gives the required total bound and the two destination cases (`WordRAM.Steps.trans`, `WordRAM.Steps.branch`).

3. The scratch agreement is maintained as the difference register and temporaries are updated; the frame relation remains available after each scratch-only change (`WordRAM.AgreeOutside.update`, `Light.Compiler.Rel.same`). The condition-size formula bounds the total instruction count, and the resulting memory therefore witnesses the claimed `Decides` property.

**Key facts.** `Light.Cond.width_eq_le_iff`, `Light.Expr.abs_val_le`, `Light.Compiler.steps_pair`, `Light.Compiler.codeAt_after_pair`, `Light.Compiler.inRange_sub`, `WordRAM.steps_sub`, `WordRAM.steps_bltz`, `WordRAM.Steps.trans`, `WordRAM.Steps.branch`, `WordRAM.AgreeOutside.update`, `Light.Compiler.Rel.same`.
