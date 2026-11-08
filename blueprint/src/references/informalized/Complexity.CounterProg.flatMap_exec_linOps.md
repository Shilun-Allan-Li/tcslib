<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CounterProgRun.lean :: Complexity.CounterProg.flatMap_exec_linOps -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Output of linear-expression operations

**Claim.** For any register assignment $\rho$ and linear expression $e$, concatenating the outputs of the micro-operations associated with $e$ gives the unary bit string of length $e$ evaluated at $\rho$.

**Proof.** Write $e=(rs,c)$, where $rs$ is the list of registers and $c$ is the constant term. The operations for $e$ first print each register in $rs$ in unary, then print $c$ copies of true. By induction on $rs$, the concatenated output of its register-printing operations is a string of true bits of length $\sum_{r\in rs}\rho(r)$. By induction on $c$, the constant operations output a string of $c$ true bits. Concatenating these strings gives a string of true bits whose length is $\sum_{r\in rs}\rho(r)+c$, precisely the value of $e$ at $\rho$.
