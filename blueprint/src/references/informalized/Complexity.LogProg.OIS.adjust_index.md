<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PreimageHost.lean :: Complexity.LogProg.OIS.adjust_index -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded Simulation of a Head Move

**Claim.** For the compiled program started from the encoded configuration and auxiliary binary index specified in the statement, some finite run reaches an encoding representing the configuration after the given input-head move. Every earlier run remains within the stated work-head bounds and satisfies the stated query-state conditions.

**Proof.** Write $p$ for the initial input-head position and distinguish whether $p=0$. The proof first records the formula for the moved position: it stays at $p$ for a stationary move, becomes $\min(p+1,|v|+1)$ for a right move, and becomes $p-1$ for a left move (`moveInputPos_val`). It also uses the initial work-head bounds to show that the starting encoding is safe (`imageCfg_safe`).

If $p=0$, a case check on the movement shows that the compiled machine already represents the desired configuration at time $0$. The earlier-time safety condition is vacuous.

Suppose $p\ne0$. For a stationary move, the compiled machine likewise starts in a representing configuration, so take time $0$. For a right move, if $p$ is the right endpoint, the boundary rule again makes the initial encoding represent the desired configuration. Otherwise the index increases by one: the increment routine reaches the encoding with index $p$ and phase ask, with all intermediate configurations safe (`index_inc`).

For a left move, first consider the subcase where $p-1=0$. One transition through the zero-test phase reaches the encoding with index $0$ and the boundary phase, by the compiled zero-step behavior (`zero_step`); the only earlier time is safe by the initial-encoding bound. In the remaining subcase, the decrement routine takes the index from $p-1$ to $p-2$ and returns to phase ask, preserving safety throughout (`index_dec`). The proof prefixes the zero-test transition to this routine, so the total time is one plus its duration. The run-decomposition law for iterated transitions justifies this concatenation (`rrun_add`), and the initial state is safe at time zero. In each case, the reached encoding represents the original machine configuration with the moved input head; the representation relation records the new index and the corresponding boundary or ask phase.

**Key facts.** `Complexity.LogProg.moveInputPos_val`, `Complexity.LogProg.OIS.imageCfg_safe`, `Complexity.LogProg.OIS.index_inc`, `Complexity.LogProg.OIS.zero_step`, `Complexity.LogProg.OIS.index_dec`, `Complexity.LogProg.rrun_add`.

**Caveat.** The supplied informal statement does not reproduce the formal theorem's exact phase and endpoint conditions; the account follows those conditions in the proof source.
