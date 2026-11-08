<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeFormat.lean :: Turing.CodeFormat.decode_of_guard_lt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Short Suffix Forces Fallback

**Claim.** If paired decoding of $\alpha$ succeeds with components $b$ and $r$, and $|r|<g(m+1)$ where $m$ is represented by $b$, then decoding $\alpha$ by $F$ returns the fallback code.

**Proof.** Unfold decoding and the full parser. The successful paired decoding supplies the bit word $b$ and suffix $r$, so the parser sets $m$ to the value represented by $b$ and tests whether the suffix has at least $F.guard\,(m+1)$ bits. The assumed strict upper bound on $|r|$ makes this length test fail. Consequently the full parser returns no result, and decoding, which uses the fallback whenever parsing fails, returns $F.fallback$.
