<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LogspaceTableau.lean :: Complexity.emit_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Circuit Encoder Runtime Bound

**Claim.** The counter program for the machine, started with zero registers at its initial label and empty output, halts on the specified unary input within the stated bound and outputs the encoding of the circuit at length $n$.

**Proof.** Let $w$ be the specified input word. The execution theorem for the encoder (`Complexity.UTab.goes_any`) supplies a completed run whose step bound is at most $\mathrm{emitC}(M)(|w|+1)^3$. The run-budget theorem (`Complexity.UTab.run_budget`) identifies the program's state after that many steps with the final register, input-position, and output data of this run; in particular, its label is halted. By the encoder-output theorem (`Complexity.UTab.tabEmit_eq`), the output of that run is the encoding of the circuit, since the second unary block has positive length. Finally, the input length satisfies $|w|+1\le (C+4)(n+1)^{d+1}$: expand its two unary blocks, use $1\le(n+1)^d$ and $n+1\le(n+1)^{d+1}$, and collect terms. Cubing this estimate and multiplying by $\mathrm{emitC}(M)$ gives the claimed bound.

**Key facts.** `Complexity.UTab.goes_any`, `Complexity.UTab.run_budget`, `Complexity.UTab.tabEmit_eq`.
