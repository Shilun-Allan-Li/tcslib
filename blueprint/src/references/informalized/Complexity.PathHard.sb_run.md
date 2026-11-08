<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathHardMachine.lean :: Complexity.PathHard.sb_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Execution of a Subtraction Routine

**Claim.** For each subtraction site and each bounded register state, the program reaches that site’s exit with its associated register cleared and the index register reduced by the original associated-register value, with truncated subtraction; the guard holds at all earlier configurations.

**Proof.** Let $q$ be the register assigned to the chosen subtraction site and let $r$ be the index register. The routine has three phases: test whether $q=0$ and exit if so; otherwise decrement $q$; then decrement $r$ and return to the first phase. The assigned register is distinct from the index register (`sb_ne`), so the two updates do not interfere. After exactly the original value of $q$ iterations, $q$ is zero and $r$ has decreased by that many units, truncated at zero; this is the subtraction-loop fact (`sub_run`). The original bound on every register is provided by the state bound (`St.Bd.toV`), and the loop’s intermediate values do not exceed those initial bounds. Applying the loop fact with the phase equations for this site yields the stated reachability and guard.

**Key facts.** `Complexity.PathHard.sb_ne`, `Complexity.PathHard.St.Bd.toV`, `Complexity.LogProg.sub_run`.
