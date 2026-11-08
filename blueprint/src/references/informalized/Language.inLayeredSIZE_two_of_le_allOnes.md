<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UnaryLanguages.lean :: Language.inLayeredSIZE_two_of_le_allOnes -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Two-Node Circuits for All-Ones Sublanguages

**Claim.** If every word in a Boolean language consists entirely of true bits, then a layered circuit family using only identity, NOT, and unbounded fan-in AND gates recognizes it with at most two non-input nodes at each input length.

**Proof.** Use the unary circuit family associated to $L$. Its gates all belong to the allowed gate set (`BoolCircuit.unaryFamily_onlyUsesGates`), and its circuit at every input length has size at most two (`BoolCircuit.unaryFamily_size_le`). The assumption that $L$ is contained in the all-ones language ensures that this family recognizes exactly $L` (`BoolCircuit.unaryFamily_language`). These properties are precisely the required witnesses.

**Key facts.** `BoolCircuit.unaryFamily_onlyUsesGates`, `BoolCircuit.unaryFamily_size_le`, `BoolCircuit.unaryFamily_language`.
