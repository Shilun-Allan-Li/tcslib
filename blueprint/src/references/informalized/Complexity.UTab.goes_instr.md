<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableauEmitterInstr.lean :: Complexity.UTab.goes_instr -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Template Instruction Execution

**Claim.** Starting from the label for a template with registers $e.f$ and input position $p$, the counter program reaches the label after the template, keeps the input position fixed, and appends the template operations evaluated at the initial registers. It increments the instruction counter; it also increments the preceding-cell counter exactly when the initial-step flag is false, within the stated step bound.

**Proof.** The template execution result (`goes_tp`) first carries the program from the template label to its successor label, producing the operations’ output using the original register values, in at most the operation-sequence length plus one steps. The hypothesis identifies that successor with the label that begins the per-template increment phase. At that label, one increment of the instruction counter moves control to the next phase (`goes_incR`); the register update facts (`ER.f_i`, `ER.set_i`) identify the resulting record as $e$ with $i$ increased by one. Now split according to the initial-step flag. If it is false, the next phase increments the preceding-cell counter and goes to the label after the template; the update facts (`ER.f_q`, `ER.set_q`) give $q+1$. If it is true, that phase jumps directly to the label after the template, leaving $q$ unchanged (`goes_goto`). Concatenating these executions uses the sequential composition rule for `Goes` (`Goes.trans`). The false-flag branch takes at most $(	ext{length}+1)+1+1=	ext{length}+3$ steps; the true-flag branch takes at most $(	ext{length}+1)+1$, which is no more than that bound. In both branches the instruction phases preserve the input position, and composition appends the template output to the existing output prefix.

**Key facts.** `Complexity.UTab.goes_tp`, `Complexity.UTab.ER.f_i`, `Complexity.UTab.ER.set_i`, `Complexity.UTab.goes_incR`, `Complexity.CounterProg.Goes.trans`, `Complexity.UTab.ER.f_q`, `Complexity.UTab.ER.set_q`, `Complexity.CounterProg.goes_goto`, `Complexity.CounterProg.Goes.mono`.
