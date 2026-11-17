<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/AlgCircuit.lean :: Randomized.AlgGate.map_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation Commutes with Ring Homomorphisms

**Claim.** Applying a ring homomorphism to the value of an algebraic gate agrees with evaluating that gate after applying the homomorphism to every input value and every value in the node list.

**Proof.** For each node index, looking it up in the mapped list gives the image under the homomorphism of the corresponding lookup in the original list, including the default value when the index is out of range. A variable gate evaluates at the corresponding input, and a constant gate evaluates to one; applying the homomorphism preserves these values. For addition, subtraction, and multiplication gates, the lookup identity together with preservation of these ring operations shows that applying the homomorphism to the original gate value gives exactly the evaluation from the mapped data.
