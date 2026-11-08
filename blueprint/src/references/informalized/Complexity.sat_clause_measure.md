<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.sat_clause_measure -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Clause Serialization Length Bound

**Claim.** For every clause $C$, its binary serialization has length at least $|C|+1$.

**Proof.** Proceed by induction on the clause. The empty clause serializes to the single terminating false bit, so its serialized length is one. For a clause formed by a literal followed by a tail, the serialization consists of that literal's code, the serialization of the tail, and the final terminator. The literal code has positive length, so adding it increases the length by at least one; the inductive bound for the tail then gives a total of at least the number of literals plus one.
