<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableauEmitterMain.lean :: Complexity.UTab.run_budget -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exact Run from a Bounded Execution

**Claim.** If every output list admits a halted execution of the associated program from its initial configuration within $B$ steps, with final registers $\rho$, input position $p$, and output equal to the initial output followed by $e$, then whenever $B\le C$, running from the initial configuration with empty output for exactly $C$ steps ends halted with registers $\rho$, input position $p$, and output $e$.

**Proof.** Apply the bounded-execution hypothesis to the empty initial output. It gives a time $t\le B$ at which the run from the initial label, zero registers, and input position zero is halted with registers $\rho$, position $p$, and output $e$. The initial configuration has precisely those zero register values; this is the zero-register identity (`Complexity.UTab.ER.zero_f`). Since $t\le B\le C$, write $C=t+(C-t)$. Runs compose across successive time intervals (`Complexity.CounterProg.run_add`), so the run for $C$ steps is the run for the remaining $C-t$ steps starting from the configuration reached at time $t$. That configuration is halted, and a halted configuration is unchanged by any further number of steps (`Complexity.CounterProg.run_of_halted`). Thus the run at time $C$ is exactly the halted configuration with registers $\rho$, position $p$, and output $e$.

**Key facts.** `Complexity.UTab.ER.zero_f`, `Complexity.CounterProg.run_add`, `Complexity.CounterProg.run_of_halted`.
