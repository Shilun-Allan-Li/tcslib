<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/AlgCircuit.lean :: Randomized.AlgCircuit.map_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Circuit evaluation commutes with ring homomorphisms

**Claim.** For commutative rings $R,S$, a ring homomorphism $f:R\to S$, a circuit $C$, and input $x\in R^n$, applying $f$ to $C(x)$ gives the evaluation of $C$ at the coordinatewise image of $x$.

**Proof.** The run of the circuit at the coordinatewise image of $x$ is the pointwise image under $f$ of the run at $x$ (`run_map`). Circuit evaluation then looks up the entry at index $|C|-1$, with zero as the default. If this lookup exists, mapping the list maps that entry to its image under $f$. If it is out of range, both lookups use the default; a ring homomorphism preserves zero, so the defaults agree as well. Thus the mapped circuit value equals the circuit value at the mapped input.

**Key facts.** `Randomized.AlgCircuit.run_map`.
