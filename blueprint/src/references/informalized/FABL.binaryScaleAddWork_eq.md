<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/ExecutableFiniteFields.lean :: FABL.binaryScaleAddWork_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Scale-Add Work Count

**Claim.** For every natural number $\ell$, the scale-add work is $2\ell$.

**Proof.** The traversal work on a list of items is its length multiplied by the work assigned to each item (`FABL.binaryConstructorTraversalWork_eq`). Applying this to the list of the first $\ell$ natural numbers gives work $\ell\cdot 2$, since that list has length $\ell$. Commutativity of multiplication identifies this with $2\ell$.

**Key facts.** `FABL.binaryConstructorTraversalWork_eq`.
