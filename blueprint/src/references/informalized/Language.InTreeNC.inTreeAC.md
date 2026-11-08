<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/TreeNCAC.lean :: Language.InTreeNC.inTreeAC -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Forgetting the tree fan-in bound

**Claim.** A language recognized by fan-in-two circuit trees of polynomial size and the stated depth is also recognized by circuit trees with polynomial size and the same depth bound, when no fan-in restriction is required.

**Proof.** Take the tree family witnessing the fan-in-two hypothesis. The conclusion asks for the same family, with the same size bound, depth bound, and recognized language; it imposes no fan-in condition. Retain the size, depth, and language witnesses and discard the fan-in witness.
