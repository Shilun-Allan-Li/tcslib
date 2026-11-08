<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satStreamRun_formula -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Formula Schedule Produces the Transform

**Claim.** If $x=\mathrm{pre}\,\mathrm{enc}(\varphi)\,\mathrm{rest}$, then running the prescribed number of rounds from formula phase, cursor $j$, and consumed length $|\mathrm{pre}|$ emits the encoding of the clause-splitting transform of $\varphi$ from cursor $j$, and finishes with its final cursor and consumed length $|\mathrm{pre}|+|\mathrm{enc}(\varphi)|$.

**Proof.** Proceed by induction on the list of clauses of $\varphi$. For the empty formula, the encoding begins with its terminating false bit. The false-bit round lemma shows that this round emits that bit, advances the consumed length by one, and enters the finished phase; this gives the claimed result for the empty formula.

For a nonempty formula $C::\varphi$, split the input prefix just after the formula marker and again after the encoding of $C$. The marker round emits true and moves from formula phase to clause phase. The clause schedule lemma then processes the encoding of $C$, emitting the output prescribed for that clause and reaching formula phase with the cursor advanced as specified by the clause transformation. Apply the induction hypothesis to the remaining formula, using the extended prefix and this new cursor. The round-count identity decomposes the total schedule into the marker round, the clause rounds, and the remaining formula rounds; concatenating their outputs yields the encoding of the transformed formula. The clause-splitting identity identifies the combined clause and tail transformations with the transformation of $C::\varphi$, and the prefix-length identities give the stated final consumed length.

**Key facts.** `Complexity.satStreamRound_false`, `Complexity.satStreamRound_marker`, `Complexity.satStreamRun_clause`, `Complexity.satStreamRun_add`, `Complexity.satStreamClause_split`.
