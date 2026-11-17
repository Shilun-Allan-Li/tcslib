<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/Cells.lean :: Light.Compiler.writable_subset_writable -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Writable Set Antitonicity

**Claim.** For a fixed machine size configuration $Z$, if $q\le q'$, then every address writable with stack bound $q'$ is writable with stack bound $q$.

**Proof.** The writable set is a union of scratch addresses, the frame pointer, stack addresses, and ordinary nonnegative addresses below the space limit. The first, second, and fourth parts do not depend on the stack bound. For the stack part, an address in `Stack q' Z.Q` has a witness $j$ with $q'\le j<Z.Q$ and address $cStack(j)$. Since $q\le q'$, the same $j$ also witnesses membership in `Stack q Z.Q`. Therefore each part of the union for bound $q'$ is contained in the corresponding part for bound $q$, yielding the inclusion.
