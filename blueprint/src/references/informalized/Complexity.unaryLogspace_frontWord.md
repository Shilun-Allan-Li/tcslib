<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LogspaceTableau.lean :: Complexity.unaryLogspace_frontWord -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Front Words Have Logarithmic-Space Query Languages

**Claim.** For all natural numbers $C,d$, the two query languages for the front word—testing whether the indexed bit is one and whether the index is less than the word length—are decidable in logarithmic space.

**Proof.** Apply the counter-program transfer theorem for unary-logspace functions (\texttt{UnaryLogspace.counterProg}) to the program associated with the front-word construction. Its required unary input function, the replicate word of $n$ ones, is unary-logspace (\texttt{unaryLogspace\_replicate}). The run-word theorem supplies the transfer theorem’s running-time and output conditions: on input $1^n$, the program halts within the stated polynomial bound and outputs the front word (\texttt{UTab.Front.run\_word}). The transfer theorem therefore yields logarithmic-space decidability of both query languages for that word.

**Key facts.** `Complexity.UnaryLogspace.counterProg`, `Complexity.unaryLogspace_replicate`, `Complexity.UTab.Front.run_word`.
