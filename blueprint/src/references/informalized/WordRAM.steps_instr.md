<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/WordRAM/Steps.lean :: WordRAM.steps_instr -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One step for a straight instruction

**Claim.** If the program at $pos$ begins with a straight instruction $i$, then one step from $(pos,m)$ reaches program counter $pos+1$ with memory equal to the effect of $i$ on $m$.

**Proof.** The code-prefix condition supplies that the instruction at $pos$ is $i$ ($\mathrm{CodeAt.head}$). Because $i$ is straight, the step characterization for straight instructions ($\mathrm{step\_straight}$) says that one step reaches the configuration with program counter $pos+1$ and memory $\mathrm{effect}(i,m)$. The one-step relation for the transition system ($\mathrm{Steps.one}$) turns this transition equality into the asserted one-step reachability.

**Key facts.** `WordRAM.CodeAt.head`, `WordRAM.step_straight`, `WordRAM.Steps.one`.
