<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/ExecutableFiniteFields.lean :: FABL.binaryModulusSearchWork_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Modulus Search Work Formula

**Claim.** For every natural number $\ell$, the binary modulus search work is $2^\ell$ times one more than the binary factor search work.

**Proof.** The traversal-work formula says that traversing a list with fixed step cost uses the list length times that cost ($\texttt{binaryConstructorTraversalWork_eq}$). Apply it to the modulus search, whose list is the list of all binary vectors of length $\ell$. That list has length $2^\ell$ ($\texttt{length_allBinaryVectors}$), and its step cost is the binary factor search work plus one. Substitution yields the claimed formula.

**Key facts.** `FABL.binaryConstructorTraversalWork_eq`, `FABL.length_allBinaryVectors`.
