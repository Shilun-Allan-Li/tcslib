<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFARM/Leaf.lean :: Complexity.LogProg.TQBFARM.lc_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Counting a Unary Variable Index

**Claim.** When the input from the pointer contains $n$ true bits, then a false terminator, then polarity bit $b$ and a suffix, the machine advances to the literal-evaluation phase with pointer $P+n+2$ and counter $V+n$, leaving the other state values as specified.

**Proof.** Induct on $n$. For $n=0$, the current bit is the false terminator. The machine takes the false branch from the counting instruction, advances past the terminator, reads the polarity bit, and reaches literal evaluation with pointer advanced by two; the variable counter is unchanged. For the successor case, the first bit is true. The machine takes the true branch, increments $V$, advances the pointer once, and the remaining suffix has the same form with $n$ true bits. Apply the induction hypothesis to this updated state. Its side condition $V\le P$ remains valid after both quantities increase by one, and the register bounds are preserved. The drop and bit-reading facts (\texttt{getD_of_drop} and \texttt{drop_succ_of_drop}) justify the observed bits and remaining suffix; the step and read lemmas assemble each transition, and endpoint equality gives the stated pointer and counter.

**Key facts.** `Complexity.LogProg.TQBFARM.read_f`, `Complexity.LogProg.TQBFARM.step_of`, `Complexity.drop_succ_of_drop`, `Complexity.getD_of_drop`, `Complexity.LogProg.TQBFARM.read_b`, `Complexity.LogProg.TQBFARM.fin_of`, `Complexity.LogProg.reach_of_eq`, `Complexity.LogProg.TQBFARM.read_t`.
