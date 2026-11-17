<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeParser.lean :: Turing.codeEraseVec -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Vector Reader Erasure Law

**Claim.** For any field reader, length, and bit string, discarding the vector parsed by the length-$n$ reader gives the same result as applying $n$ times the skipper that discards each field's value and retains its suffix.

**Proof.** We induct on $n$. When $n=0$, the vector reader returns the empty vector and the unchanged input, while zero repetitions of the skipper also return the unchanged input. For the step from $n$ to $n+1$, the reader first parses one value and suffix, then parses a length-$n$ vector from that suffix. After discarding the value, the remaining computation is precisely the length-$n$ reader's suffix result. By the induction hypothesis, this equals applying the skipper $n$ times to that suffix. The fact that binding a reader to a continuation of the suffix is unchanged if we first discard the reader's value and then bind the continuation (`codeErase_bind`) identifies this two-stage erasure with one initial skip followed by those $n$ skips. This is exactly $n+1$ repetitions of the skipper.

**Key facts.** `Turing.codeErase_bind`.
