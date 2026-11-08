<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeSimulator.lean :: Turing.fin_cons_two -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Consing onto a Two-Entry Function

**Claim.** For optional Boolean values $w_0,w_1$, consing $w_0$ onto the constant one-entry function with value $w_1$ yields the function taking $w_0$ at index $0$ and $w_1$ at index $1$.

**Proof.** Check equality at each of the two indices. At index $0$, the cons operation returns $w_0$, which is also the specified function's value there. At index $1$, it returns the value of the tail function, namely $w_1$, again agreeing with the specified function.
