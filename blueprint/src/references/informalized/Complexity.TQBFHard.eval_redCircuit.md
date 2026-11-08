<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFHard.lean :: Complexity.TQBFHard.eval_redCircuit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of the Reduction Circuit

**Claim.** Under the stated time-computation hypothesis for the verifier machine, the reduction circuit on input bits supplied by a Boolean sequence evaluates to the predicate on the paired input consisting of $x$ and the corresponding finite initial segment of that sequence.

**Proof.** Let $\sigma$ be the finite list of the first $\mathrm{redM}(N,d,c,|x|)$ bits of $\tau$. Its length is therefore exactly the reduction circuit’s input width. The circuit’s tableau evaluation theorem (`Complexity.cfgTab_eval`) identifies its output with whether the verifier emits true during its allotted number of steps, when run on the circuit’s fixed prefix followed by its input assignment. Here that prefix is $\mathrm{pairEncode}(x,[])$, so appending $\sigma$ gives $\mathrm{pairEncode}(x,\sigma)$. By the verifier’s computation hypothesis, it computes the one-bit output $\mathrm{predB}(\mathrm{pairEncode}(x,\sigma))$ within the prescribed polynomial time. The time bound `Complexity.TQBFHard.time_le` shows that this run fits within the tableau’s time parameter; monotonicity of computation time (`Turing.FinTM.ComputesInTime.mono`) extends the run to that bound. Finally, the theorem identifying emitted output with the verifier’s computed bit (`Complexity.decide_emits_eq_of_computesInTime`) turns the tableau’s acceptance indicator into precisely that predicate value.

**Key facts.** `Complexity.cfgTab_eval`, `Complexity.TQBFHard.time_le`, `Turing.FinTM.ComputesInTime.mono`, `Complexity.decide_emits_eq_of_computesInTime`.
