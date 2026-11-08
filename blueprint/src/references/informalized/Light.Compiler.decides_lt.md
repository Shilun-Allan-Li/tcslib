<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/Conditions.lean :: Light.Compiler.decides_lt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Compiled strict inequality test

**Claim.** Under the stated framing, boundedness, code-location, width, and safety assumptions, the compiled strict inequality test runs in at most its size, reaching the position after the test when $a<b$ and the target otherwise, while preserving memory outside the scratch cells.

**Proof.** 1. The condition-width bound gives individual width bounds for $a$ and $b$. Evaluate their compiled expressions in sequence; the resulting temporary cells contain their values, and memory is unchanged outside the scratch cells (`Light.Cond.width_lt_le_iff`, `Light.Compiler.steps_pair`). The code-location lemma places the remaining instructions immediately afterward (`Light.Compiler.codeAt_after_pair`).

2. The next subtraction computes $D=b-a$, followed by a subtraction of $1$, so the tested quantity is $b-a-1$. The value is representable by the subtraction bound, using safety and boundedness to bound $a$ and $b$ (`Light.Expr.abs_val_le`, `Light.Compiler.inRange_sub`). The branch goes to $l$ precisely when $b-a-1<0$, equivalent for integers to $a\ge b$. Otherwise it falls through, and $a<b$. Thus the branch has exactly the required destinations. The two subtractions and conditional branch each take one step; composing them with expression evaluation gives the asserted run (`WordRAM.steps_sub`, `WordRAM.steps_bltz`, `WordRAM.Steps.trans`, `WordRAM.Steps.branch`).

3. Each write updates only scratch cells, so the memory agreement outside them is preserved (`WordRAM.AgreeOutside.update`). The condition-size formula bounds the complete run by the test's size, yielding the required `Decides` witness.

**Key facts.** `Light.Cond.width_lt_le_iff`, `Light.Compiler.steps_pair`, `Light.Compiler.codeAt_after_pair`, `Light.Expr.abs_val_le`, `Light.Compiler.inRange_sub`, `WordRAM.steps_sub`, `WordRAM.steps_bltz`, `WordRAM.Steps.trans`, `WordRAM.Steps.branch`, `WordRAM.AgreeOutside.update`.
