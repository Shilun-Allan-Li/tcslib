<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clA5Emit_exact -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exact Tableau Clause Chunks

**Claim.** For the packed records of $x$ at cursor $j$, the emitter returns the $j$th tableau clause-group chunk through the schedule's last round, including the terminator on the final round, and returns the empty word after that round.

**Proof.** For the packed input, decoding its outer pair shows that the cursor field has length exactly $j$. The stored-header identity (`clA5Stored_exact`) also identifies the stored instance as $x$ and its stored round as the schedule's last round. The exact fragment identity (`clA5Fragment_exact`) then says that the emitted fragment is the serialization of the $j$th tableau group, with an empty group when the index is out of range. Substituting these identities into the emitter definition leaves its round check: when $j$ is at most the last round, it appends the terminator precisely if $j$ is that last round; when $j$ exceeds the last round, it returns empty. This is exactly the defined clause chunk (`clChunk`) and the claimed behavior.

**Key facts.** `Turing.pairDecode_pairEncode`, `Complexity.clA5Stored_exact`, `Complexity.clA5Fragment_exact`.
