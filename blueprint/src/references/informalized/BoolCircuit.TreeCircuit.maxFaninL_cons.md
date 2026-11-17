<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Basic.lean :: BoolCircuit.TreeCircuit.maxFaninL_cons -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Maximum fanin after adjoining a circuit

**Claim.** The maximum fanin of the list formed by placing $c$ before $cs$ is the maximum of the fanin of $c$ and the maximum fanin in $cs$.

**Proof.** By definition, the maximum fanin of a list is the right fold that takes the maximum of each circuit's fanin, starting from $0$. Folding over the list whose first element is $c$ gives the maximum of $c$'s fanin and the fold over the remaining list, namely the maximum fanin of $cs$.
