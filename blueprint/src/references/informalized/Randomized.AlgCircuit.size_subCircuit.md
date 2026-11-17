<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/AlgCircuit.lean :: Randomized.AlgCircuit.size_subCircuit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Size of a subcircuit construction

**Claim.** For any two arithmetic circuits $C$ and $C'$ on the same number of inputs, the circuit formed by placing their gate lists together, shifting the node references of the second list by the size of the first, and appending a subtraction gate has size $\mathrm{size}(C)+\mathrm{size}(C')+1$.

**Proof.** The constructed gate list concatenates the gates of $C$, the shifted gates of $C'$, and one final subtraction gate. Concatenation lengths add, shifting preserves the length of the second list, and the final singleton contributes one. Thus its length, and hence the subcircuit's size, is $\mathrm{size}(C)+\mathrm{size}(C')+1$.
