<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/CounterProgPolyTime.lean :: Complexity.CounterProg.polyTimeComputable_of_goes -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Computability from Bounded Runs

**Claim.** If, on every input, the counter program reaches a halted state with output equal to the input's image under $f$ within a polynomial number of steps, then a finite binary-alphabet Turing machine computes $f$ in polynomial time.

**Proof.** Fix an input $x$. The hypothesis supplies register values, a read position, and a bounded reachability statement that holds for every prior output. Apply it with the empty prior output to obtain a run of at most $C(|x|+1)^c$ steps from the state with zero registers, read position zero, and empty output. By the definition of the initial state, this is precisely the counter program's run from its initial state; the obtained terminal state is halted and its output is $f(x)$. Thus the hypotheses of the polynomial-time simulation theorem are satisfied for every input, and that theorem yields a finite binary-alphabet Turing machine computing $f$ in polynomial time (\texttt{polyTimeComputable}).

**Key facts.** `Complexity.CounterProg.polyTimeComputable`.
