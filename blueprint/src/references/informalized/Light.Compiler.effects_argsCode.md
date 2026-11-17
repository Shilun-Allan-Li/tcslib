<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/CallFrames.lean :: Light.Compiler.effects_argsCode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Compiled Argument Evaluation

**Claim.** Under the framing, width, safety, and temporary-space hypotheses, the compiled argument code places each expression value in its corresponding temporary cell and leaves memory unchanged outside the designated temporary cells.

**Proof.** Proceed by induction on the list of expressions, generalizing the starting temporary index and memory. For the empty list, there are no output cells to check and memory is unchanged. For a nonempty list $e::es$, the hypotheses give the required width and safety bounds for $e$ and for every expression in the tail. First execute the compiled code for $e$ at index $k$: the compiled-expression effect theorem gives its value in cell $k$ and confines its changes to the temporary region (`Light.Compiler.effects_compileExpr_of_width`). This region lies within the scratch region (`Light.Compiler.temps_subset_scratch`), so the frame relation still holds for the memory after compiling $e$ (`Light.Compiler.Framed.same`). Apply the induction hypothesis to the tail starting at $k+1$. Since argument code concatenates the head’s code with the tail’s code, the effects of the whole list are these two executions in sequence (`WordRAM.effects_append`). The first output is the head value, read from cell $k$ after the tail execution because the tail preserves that cell; subsequent outputs are exactly those supplied by the induction hypothesis, with indices shifted by one. Finally, the two executions’ preservation guarantees compose to show that the whole computation changes memory only within the allowed temporary region (`WordRAM.AgreeOutside.trans` and `WordRAM.AgreeOutside.mono`).

**Key facts.** `Light.Compiler.effects_compileExpr_of_width`, `Light.Compiler.temps_subset_scratch`, `Light.Compiler.Framed.same`, `WordRAM.effects_append`, `WordRAM.AgreeOutside.read`, `WordRAM.AgreeOutside.trans`, `WordRAM.AgreeOutside.mono`.
