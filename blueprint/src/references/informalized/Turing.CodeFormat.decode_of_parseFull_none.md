<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeFormat.lean :: Turing.CodeFormat.decode_of_parseFull_none -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Failed Parse Gives Fallback

**Claim.** For every code format $F$ and Boolean word $\alpha$, if the full parser for $F$ fails on $\alpha$, then decoding $\alpha$ by $F$ returns its fallback code.

**Proof.** Decoding takes the first component of a successful full parse and uses the fallback when the parse returns no result. Under the hypothesis that the full parse of $\alpha$ is none, this definition therefore gives $F.fallback$.
