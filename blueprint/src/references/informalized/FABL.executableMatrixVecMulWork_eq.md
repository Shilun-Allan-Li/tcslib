<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/AlmostKWiseAlgorithm.lean :: FABL.executableMatrixVecMulWork_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Matrix Vector Multiplication Work

**Claim.** For all natural numbers $m,n$, executable matrix-vector multiplication work is $n(2m+1)$.

**Proof.** The traversal-work identity (FABL.binaryConstructorTraversalWork_eq) says that traversing a list costs its length times the per-item work. Applied to the list of the first $n$ natural numbers, whose length is $n$, with per-item work $2m+1$, this gives $n(2m+1)$.

**Key facts.** `FABL.binaryConstructorTraversalWork_eq`.
