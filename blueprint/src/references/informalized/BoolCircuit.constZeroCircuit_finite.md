<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UnaryLanguages.lean :: BoolCircuit.constZeroCircuit_finite -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Finiteness of the zero circuit

**Claim.** For every natural number $n$, each layer of the zero circuit with $n$ inputs has a finite set of nodes.

**Proof.** There are three layers. The initial layer has node type $\mathrm{Fin}(n)$, which is finite, and each of the two subsequent layers has node type $\mathrm{Unit}$, which is finite. Hence every layer has finitely many nodes.
