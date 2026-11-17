<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/CircuitSatReductionMachine.lean :: BoolCircuit.CktSatReduction.Emitter.emTM_computes -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gate-Clause Machine Running Time

**Claim.** The finite-state multi-tape machine computes the gate-clause encoding on every Boolean input of length $n$ within exactly $200(n+1)^2$ steps.

**Proof.** Fix an input word $w$. Its initial machine configuration is the configuration encoding phase $n$, vertex and argument counters all zero, with the input head at the start, blank work tapes, and empty output; the blank-tape description follows from $\texttt{ones\_zero}$. Apply the machine's main-run estimate to this configuration. It gives a halting time $T$ no greater than $(|w|+1)\,200(|w|+1)=200(|w|+1)^2$, and output equal to the initial output followed by the emitter's output on $w$, which is the gate-clause encoding. A halted configuration remains fixed for every further step ($\texttt{runFrom\_of\_halt}$), so the computation can be extended from $T$ to the stated bound without changing its state or output, using the run-addition law ($\texttt{runFrom\_add}$). The characterization of computation in time by halting and having the specified output at that time ($\texttt{FinTM.computesInTime\_iff}$) then gives the result.

**Key facts.** `Turing.UnaryTape.ones_zero`, `BoolCircuit.CktSatReduction.Emitter.em_main_run`, `Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.runFrom_of_halt`, `Turing.FinTM.computesInTime_iff`.
