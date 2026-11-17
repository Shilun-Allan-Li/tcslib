<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Finite.lean :: Turing.FinTM.Computes.exists_computesInTime_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Outputs of a function-computing machine

**Claim.** If a finite Turing machine computes $g$, then there exists a time at which it halts on $x$ with output $w$ if and only if $w=g(x)$.

**Proof.** Because the machine computes $g$, on input $x$ it halts at some time $t$ with output $g(x)$. If it also halts at a time $s$ with output $w$, uniqueness of output across halting times gives $w=g(x)$ (\texttt{Turing.FinTM.ComputesInTime.output_unique}). Conversely, if $w=g(x)$, the already chosen computation at time $t$ is a computation with output $w$, so such a time exists.

**Key facts.** `Turing.FinTM.ComputesInTime.output_unique`.
