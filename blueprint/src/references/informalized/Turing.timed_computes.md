<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Universal.lean :: Turing.timed_computes -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Timed computation of a bounded answer

**Claim.** For every effective machine coding scheme $c$, code string $\alpha$, input $x$, and time bound $t$, the timed universal machine on $\langle\langle\operatorname{bin}(t),\alpha\rangle,x\rangle$ halts with the bounded answer of the decoded machine after $t$ steps, in exactly $(S+B+14)(t+1)^2$ steps, where $S$ and $B$ are the startup and block bounds.

**Proof.** First, the timed universal machine reaches a framed interpreter configuration after some startup time $s$, with $s\le 4|\operatorname{bin}(t)|+S$ (`timed_initialized`). Starting from this checkpoint, the timed interpreter reaches its bounded answer after some additional $d$ steps (`timed_interpret_finishes`), using the fact that the clock word has value $t$ (`timedValue_bits`). Since the binary representation has length at most $t$ (`length_bits_le_self`), the startup and interpretation bounds combine to give $s+d\le(S+B+14)(t+1)^2$ by the quadratic cost estimate (`timed_cost_bound`). The framed simulation preserves the timed interpreter's run inside the captured machine (`timedFrame_run`). Consequently, concatenating the startup and simulation runs gives a computation with the required output and halt state at time $s+d$; the equivalence between this run description and computation in time is `computesInTime_iff`. Finally, monotonicity extends the computation to the stated exact time bound (`ComputesInTime.mono`).

**Key facts.** `Turing.timed_initialized`, `Turing.timed_interpret_finishes`, `Turing.timedValue_bits`, `Turing.length_bits_le_self`, `Turing.timed_cost_bound`, `Turing.MultiTapeTM.runFrom_add`, `Turing.timedFrame_run`, `Turing.FinTM.computesInTime_iff`, `Turing.FinTM.ComputesInTime.mono`.
