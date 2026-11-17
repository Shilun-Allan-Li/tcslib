<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Basic.lean :: BoolCircuit.TreeCircuit.maxFaninL_nil -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Empty-list maximum fanin

**Claim.** The maximum fanin aggregated over the empty list of Boolean circuits is $0$.

**Proof.** The list maximum fanin is defined as a fold taking maxima, with starting value $0$. Since the empty list has no entries to fold over, the result is $0$.
