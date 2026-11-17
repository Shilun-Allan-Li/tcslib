<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LogspaceTableauFront.lean :: Complexity.UTab.Front.goes_read -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reading a Unary Input Prefix

**Claim.** If the input consists of $n$ ones, then for every $j\le n$ the program returns to its reading label with the first register equal to $j$, all other registers zero, input position $j$, and exactly $j$ ones appended, in at most $3j$ steps.

**Proof.** Induct on $j$. For $j=0$, the zero-step run from `goes_nil` gives the claim. For the successor step, the induction hypothesis gives the run for the first $j$ input symbols. Because $j<n$, the next symbol is $1$, so the read instruction consumes it and moves to the next label (`goes_rd_true`). The following instruction increments the first register (`goes_inc`), and the next prints one and returns to the reading label (`goes_out`). Compose these runs with the induction-hypothesis run by `Goes.trans`. The increment and register-update facts (`rv_X`, `upd_X`) show that the first register has become $j+1$ and the others remain zero; the output is the first $j+1$ ones. `Goes.congr` aligns these state and output descriptions, and the three added steps give the bound $3j+3=3(j+1)$.

**Key facts.** `Complexity.UTab.Front.goes_nil`, `Complexity.CounterProg.goes_rd_true`, `Complexity.CounterProg.goes_inc`, `Complexity.CounterProg.goes_out`, `Complexity.CounterProg.Goes.trans`, `Complexity.UTab.Front.rv_X`, `Complexity.UTab.Front.upd_X`, `Complexity.CounterProg.Goes.congr`.
