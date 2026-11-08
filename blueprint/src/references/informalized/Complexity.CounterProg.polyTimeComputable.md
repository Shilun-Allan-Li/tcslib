<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/CounterProgPolyTime.lean :: Complexity.CounterProg.polyTimeComputable -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Simulation of a Counter Program

**Claim.** If a counter program with finitely many labels halts with output $f(x)$ within $C(|x|+1)^c$ steps on every input $x$, then $f$ is computable by a finite binary-alphabet Turing machine in polynomial time.

**Proof.** Use the Turing-machine simulation of the counter program. For an input $x$ on which the counter program halts after $t$ steps, the simulation theorem gives the same output and a running time of $t(2t+3)$ (\texttt{exists\_tm}). By the assumed bound, $t\le C N$, where $N=(|x|+1)^c$. Since $N\ge1$, the simulated time is at most $(CN)(2CN+3N)=(2C^2+3C)N^2$. As $N^2=(|x|+1)^{2c}$, the same machine computes $f$ within the polynomial bound with constants $2C^2+3C$ and $2c$. The ability to extend a computation's time bound to a larger one ensures this bound applies in the definition of computation within a specified time (\texttt{ComputesInTime.mono}).

**Key facts.** `Complexity.CounterProg.exists_tm`, `Turing.FinTM.ComputesInTime.mono`.
