<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/Simulation.lean :: Light.Compiler.sim_set -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Variable Assignment Simulation

**Claim.** If expression $e$ is safe in $\sigma$, assigning its value to local variable $x$ is simulated from $\sigma$ to the state with that local variable updated and memory unchanged, with cost $\operatorname{cost}(e)+1$.

**Proof.** Fix a valid starting configuration. The assignment's width bound ensures both that $x$ is a valid local slot and that the expression fits in the available temporaries. Split its code into expression evaluation followed by the two-instruction local-variable update. Evaluating the expression places $e$'s value in temporary $T_0$ and alters only temporary cells; these lie in the scratch region, so the frame relation is preserved. The two update instructions then store that value in the stack cell for local variable $x$, yielding the relation for the updated state and agreement outside the writable region. The machine runs concatenate, and their lengths total the expression's code length plus two; the expression-code length equals its size. This gives the claimed cost bound, and the endpoint is the position after the assignment code.

**Key facts.** `Light.Stmt.width_set_le_iff`, `Light.Compiler.codeAt_set`, `Light.Compiler.effects_compileExpr_of_width`, `Light.Compiler.temps_subset_scratch`, `Light.Compiler.Framed.same`, `Light.Compiler.steps_straight`, `Light.Compiler.length_compileExpr`, `Light.Compiler.steps_setVar`, `Light.Compiler.le_stepsPerStep_mul`, `Light.Compiler.scratch_subset_writable`, `WordRAM.AgreeOutside.mono`, `WordRAM.AgreeOutside.trans`, `WordRAM.Steps.trans`, `WordRAM.Steps.cast_pos`.
