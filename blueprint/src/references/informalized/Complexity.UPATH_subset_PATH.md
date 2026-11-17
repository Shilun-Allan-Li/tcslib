<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/UPath.lean :: Complexity.UPATH_subset_PATH -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Undirected Reachability Encodings Are Path Encodings

**Claim.** If a binary string encodes a finite undirected graph with designated vertices joined by a path, then it is an encoding of a graph with designated vertices joined by a path, without any symmetry requirement on the adjacency relation.

**Proof.** Unpack membership in `UPATH`: there are a graph size, an adjacency relation, designated source and target, and an encoding equality, together with symmetry and reachability. Keep the size, relation, vertices, encoding equality, and reachability; the definition of `PATH` requires precisely these data and omits only the symmetry condition. They therefore witness membership in `PATH`.
