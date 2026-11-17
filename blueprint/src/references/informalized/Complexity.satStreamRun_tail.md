<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satStreamRun_tail -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Tail-Phase Clause Schedule

**Claim.** If $x=\mathrm{pre}\,\mathrm{enc}(C)\,\mathrm{rest}$, then running $|C|+1$ rounds from tail phase, cursor $j$, and consumed length $|\mathrm{pre}|$ emits the pending tail output for $C$ at cursor $j$, and ends in formula phase with the final cursor and consumed length $|\mathrm{pre}|+|\mathrm{enc}(C)|$.

**Proof.** Induct on the clause. For the empty clause, its encoding is just the terminating false bit. The false-bit round lemma says that, from tail phase, this round emits false, advances the consumed length by one, and returns to formula phase; these are exactly the empty clause's pending tail output and final state.

For a clause $l::C$, divide its encoding into the encoding of $l$ followed by the encoding of $C$. The literal-round lemma processes $l$ in tail phase. If $C$ is empty, the delimiter following $l$ does not trigger a fresh-variable split, and the remaining single round is covered by the induction case for the empty tail. If $C$ is nonempty, the next encoded bit is the clause marker, so the literal round emits the fresh-variable split output and advances the cursor from $j$ to $j+1$. Apply the induction hypothesis to $C$ from that cursor and with the consumed prefix extended by the encoding of $l$. The outputs concatenate to the definition of the pending tail output for $l::C$, while the consumed-length and cursor updates give the stated final state.

**Key facts.** `Complexity.satStreamRound_false`, `Complexity.satStreamRound_literal`.
