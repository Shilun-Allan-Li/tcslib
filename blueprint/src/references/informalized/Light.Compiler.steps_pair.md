<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/Conditions.lean :: Light.Compiler.steps_pair -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of two expressions

**Claim.** Under the stated frame, width, safety, and code-prefix hypotheses, the compiled code for $a$ followed by the compiled code for $b$ executes for $a.\mathrm{size}+b.\mathrm{size}$ steps. The resulting memory has their values in temporary slots $0$ and $1$, respectively, and agrees with the initial memory outside the scratch-address set for $F$.

**Proof.** First apply the expression-effects theorem (`Light.Compiler.effects_compileExpr_of_width`) to $a$ at temporary slot $0$. It says that executing its compiled effects puts the value of $a$ in that slot and changes memory only within $\mathrm{Temps}(0,F)$. Since this set is contained in the scratch set, the resulting memory still represents the same framed state, by frame preservation (`Light.Compiler.Framed.same`). Apply the same expression-effects theorem to $b$ at slot $1$ in this updated frame. Its effects put the value of $b$ in slot $1$ and alter memory only within $\mathrm{Temps}(1,F)$.

Every instruction in both expression compilations is straight (`Light.Compiler.straight_compileExpr`). The code-prefix hypothesis supplies the prefix for their concatenation (`WordRAM.CodeAt.left`), so the straight-code execution theorem (`WordRAM.steps_straight`) realizes the combined effects as machine steps. The compiled length theorem (`Light.Compiler.length_compileExpr`) identifies the number of steps with $a.\mathrm{size}+b.\mathrm{size}$, and effects of concatenated code compose in execution order (`WordRAM.effects_append`). Because slot $0$ lies outside $\mathrm{Temps}(1,F)$, the second computation preserves the value already placed there (`WordRAM.AgreeOutside.read`). Finally, both computations' memory changes are contained in the scratch set; transitivity of agreement (`WordRAM.AgreeOutside.trans`) gives agreement with the initial memory outside that set.

**Key facts.** `Light.Compiler.effects_compileExpr_of_width`, `Light.Compiler.Framed.same`, `Light.Compiler.straight_compileExpr`, `WordRAM.CodeAt.left`, `WordRAM.steps_straight`, `Light.Compiler.length_compileExpr`, `WordRAM.effects_append`, `WordRAM.AgreeOutside.read`, `WordRAM.AgreeOutside.trans`, `Light.Compiler.temps_subset_scratch`.
