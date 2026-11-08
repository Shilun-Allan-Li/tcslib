<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/CircuitEvalRun.lean :: BoolCircuit.CircuitEval.onesFrom_self -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Empty Interval at Its Endpoint

**Claim.** For every natural number $n$, the tape marking the cells in $[n,n)$ is the empty tape.

**Proof.** Fix an integer cell $c$. Its value on the interval tape can be true only if $n\le c<n$, which is impossible. Thus the interval tape is blank at every cell. The tape defined by the empty list is also blank everywhere, so the two tapes agree pointwise and hence are equal.
