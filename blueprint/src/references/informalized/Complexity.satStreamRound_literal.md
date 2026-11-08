<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satStreamRound_literal -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Round at a Complete Literal

**Claim.** When the unconsumed input begins with the encoding of a literal and the phase is neither $0$ nor $4$, one round emits the prescribed literal output and updates the cursors and phase according to whether the phase is $3$ and the remainder begins with $1$.

**Proof.** Dropping the consumed prefix $p$ from the input leaves precisely the encoding of $\ell$ followed by $r$. That encoding begins with $1$, and the literal parser recognizes it and returns $(\ell,r)$ (\texttt{Complexity.satStream_parseLit}). The excluded phases rule out the finished and marker branches, so the round follows the parsed-literal branch. If the phase is $3$ and $r$ begins with $1$, it emits the two fresh-variable encodings, the intervening bits $0,1$, and then the encoding of $\ell$; it advances the fresh cursor to $j+1$, advances the consumed length by the encoded literal length, and remains in phase $3$. In every other case it emits only the encoding of $\ell$, leaves the fresh cursor at $j$, advances the consumed length by that same encoded length, and enters phase $2$ if the old phase was $1$, or phase $3$ otherwise.

**Key facts.** `Complexity.satStream_parseLit`.
