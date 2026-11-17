<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/SizeClasses.lean :: Language.allOnes_inLayeredSIZE_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Constant Layered Size for All Ones

**Claim.** The all-ones language is recognized by a finite-layer Boolean circuit family using only identity, NOT, and unbounded fan-in AND gates, with size at most $1$ at every input length.

**Proof.** Use the family of circuits constructed for the all-ones language. Its gates all belong to the specified standard gate set ( `BoolCircuit.allOnesFamily_onlyUsesGates`), its language is exactly the all-ones language ( `BoolCircuit.allOnesFamily_language`), and each circuit has size exactly $1$ ( `BoolCircuit.allOnesCircuit_size`). The size equality implies the required upper bound.

**Key facts.** `BoolCircuit.allOnesFamily_onlyUsesGates`, `BoolCircuit.allOnesCircuit_size`, `BoolCircuit.allOnesFamily_language`.
