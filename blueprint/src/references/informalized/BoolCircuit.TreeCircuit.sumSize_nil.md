<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Basic.lean :: BoolCircuit.TreeCircuit.sumSize_nil -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Empty-list size sum

**Claim.** The sum of the sizes in the empty list of Boolean circuits on $n$ variables is $0$.

**Proof.** By definition, this sum is the right fold of the empty list, whose initial value is $0$. Hence it equals $0$.
