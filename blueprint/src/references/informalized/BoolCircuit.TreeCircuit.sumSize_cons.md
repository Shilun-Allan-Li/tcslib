<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Basic.lean :: BoolCircuit.TreeCircuit.sumSize_cons -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Size Sum Over a Cons List

**Claim.** For a circuit $c$ and a finite list of circuits $cs$, the sum of sizes in $c::cs$ is $\mathrm{size}(c)$ plus the sum of sizes in $cs$.

**Proof.** The sum of sizes is defined by folding from the right, adding each circuit's size to the accumulated sum. Unfolding this definition at the head of the list gives the size of $c$ plus the sum over the tail.
