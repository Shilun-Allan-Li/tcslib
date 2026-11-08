<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/SmallBiasOutputBit.lean :: FABL.executableBinaryDotProductWork_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Work of the binary dot product

**Claim.** For every $$-length input, the assigned work of the executable binary dot product is $2\ell$.

**Proof.** The traversal processes the list of indices from $0$ through $\ell-1$, charging work $2$ for each item. The traversal-work formula (\texttt{binaryConstructorTraversalWork\_eq}) says that total work is list length times per-item work. The list has length $\ell$, so the total is $\ell\cdot2=2\ell$.

**Key facts.** `FABL.binaryConstructorTraversalWork_eq`.
