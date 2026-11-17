<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UnaryLanguages.lean :: BoolCircuit.unaryFamily_language -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Language of the Unary Family

**Claim.** If every word in $L$ consists entirely of true bits, then the language recognized by the unary family equals $L$.

**Proof.** First observe that, for any word $w$, membership in $L$ is equivalent to the conjunction that $w$ consists entirely of true bits and that the length-$w$ all-true word belongs to $L$. Indeed, membership in $L$ gives the first condition by the assumption $L\subseteq\mathrm{Language.allOnes}$; the characterization of all-true words says that $w$ is the length-$w$ all-true word, so the second condition follows. Conversely, the first condition identifies $w$ with that all-true word, and the second condition then gives $w\in L$. Now fix $w$ and use the characterization of membership in a circuit family's language as acceptance of $w$ by its length-$w$ circuit (`BoolCircuit.LayeredCircuitFamily.mem_language_iff`). If the length-$w$ all-true word is in $L$, the unary family uses the all-ones circuit (`BoolCircuit.unaryFamily_circuit_of_mem`); its language is exactly the all-true words (`BoolCircuit.allOnesFamily_language`). Thus acceptance is equivalent to the first condition above, and the second condition is already true. If the all-true word is not in $L$, the family uses the constant-zero circuit (`BoolCircuit.unaryFamily_circuit_of_not_mem`), whose output is zero on every input (`BoolCircuit.constZeroCircuit_eval₁`); acceptance is false, matching the conjunction because its second condition fails. These two cases establish equality of the recognized language and $L$.

**Key facts.** `BoolCircuit.LayeredCircuitFamily.mem_language_iff`, `Language.mem_allOnes_iff`, `BoolCircuit.unaryFamily_circuit_of_mem`, `BoolCircuit.allOnesFamily_language`, `BoolCircuit.unaryFamily_circuit_of_not_mem`, `BoolCircuit.constZeroCircuit_eval₁`.
