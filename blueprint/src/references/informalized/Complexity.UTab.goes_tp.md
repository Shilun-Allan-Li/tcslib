<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableauEmitterInstr.lean :: Complexity.UTab.goes_tp -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Execution of a Template Program

**Claim.** Starting at the label for a template $\theta$, the counter program reaches the label following $\theta$ with its registers and input position unchanged, appending the output obtained by executing the template operations with the given register values, in at most the template length plus one steps.

**Proof.** Regard the template's operation list as a finite program whose position $i$ is represented by the label carrying $\theta$ and counter $i$. The bound on template length (`Complexity.UTab.length_tmpl_le`) ensures that every position through the end of the list fits within the program's counter range. At each position before the end, the program instruction prints the operation there—either the indicated bit or the register's unary value—and advances to the next position. At the end it jumps to $\theta$'s successor label without changing registers, input position, or output. Thus the general template-execution fact (`Complexity.CounterProg.goes_tmpl`) applies: the output appended is the concatenation of the executions of all operations, namely the template's specified output, and the run takes at most the list length plus one steps.

**Key facts.** `Complexity.UTab.length_tmpl_le`, `Complexity.CounterProg.goes_tmpl`.
