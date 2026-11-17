<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Transducer.lean :: Complexity.transducerTM_computes -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-Pass Transducer Computation

**Claim.** The binary Turing machine implementing the given transition and emission functions halts with the transducer’s output on every input of length $n$ within $n+1$ steps.

**Proof.** Fix an input word $x$. Apply the suffix-run theorem to the whole input, taking the suffix to be $x$, the starting state to be $q_0$, and the initial configuration to be the machine’s initial configuration. The suffix is obtained by dropping zero symbols, and the initial state and head position meet the theorem’s hypotheses. It follows that after $|x|+1$ steps the machine is halted and its output is the initial empty output followed by the transducer output on $x$. The characterization of computation in time (\texttt{computesInTime\_iff}) turns these halting and output equalities into the required time-computation statement.

**Key facts.** `Complexity.transducer_run`, `Turing.FinTM.computesInTime_iff`.
