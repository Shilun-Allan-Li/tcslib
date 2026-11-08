<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satStreamClause_split -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Clause splitting and emitted serialization

**Claim.** For every clause $C$ and cursor $j$, serializing the clauses produced by splitting $C$ at $j$, with a clause marker before each, gives a clause marker followed by the emitted body of $C$; the returned cursors also agree.

**Proof.** Proceed by cases on the shape of $C$. For the empty clause, splitting produces the single empty clause, and both sides reduce to a clause marker followed by the empty-clause terminator; the cursor stays at $j$. For a singleton clause, the split produces that clause unchanged, so its marked serialization agrees with the emitted body and the cursor again stays fixed. For a clause with at least two literals, write it as $a :: b :: C'$. The defining equations reduce the claim to the chain-versus-tail identity: splitting the chain beginning with $a$ and $b$ serializes to a marker followed by the serializations of $a$ and $b$ and the tail emitted from $C'$, while both constructions return the same final cursor (satStreamTail_chain).

**Key facts.** `Complexity.satStreamTail_chain`.
