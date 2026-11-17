<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeParser.lean :: Turing.codeReadWrite_sound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Soundness of write decoding

**Claim.** If the optional-write reader succeeds on a bit string $x$, returning an optional work-tape write $b$ and suffix $r$, then $x$ is the two-bit encoding of $b$ followed by $r$.

**Proof.** The reader can succeed only when the input has at least two bits. Split off those first two bits and consider their four possibilities. The reader’s defining clauses show that $00$, $01$, $10$, and $11$ return, respectively, no write, an explicitly empty option, a write of false, and a write of true, with the unconsumed tail as suffix. Since the successful result specifies $b$ and $r$, the first two bits must be the encoding of $b$ and the tail must be $r$. Thus the input is that encoding followed by $r$.
