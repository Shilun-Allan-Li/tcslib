<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomWalkCover.lean :: Randomized.RegularMultigraph.exists_endpoint_eq_two_mul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A Walk of Prescribed Length

**Claim.** Under the stated connectivity and nonbipartiteness hypotheses, any two vertices can be joined by a neighbor-slot list of length exactly $2|V|$.

**Proof.** First choose, using the even-walk bound ($\texttt{exists\_even\_word}$), a list $w$ ending at $v$ from $u$, of even length strictly less than $2|V|$. The difference $2|V|-|w|$ is therefore a nonnegative even integer, say $2m$. The lengthening result ($\texttt{exists\_word\_add}$) extends this walk by $2m$ choices while preserving its endpoint. The resulting list has length $|w|+2m=2|V|$ and still ends at $v$.

**Key facts.** `Randomized.RegularMultigraph.exists_even_word`, `Randomized.RegularMultigraph.exists_word_add`.
