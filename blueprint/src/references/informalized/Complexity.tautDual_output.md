<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Tautology.lean :: Complexity.tautDual_output -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Guarded Dual Output Identity

**Claim.** For every binary string $x$, the guarded dual output equals the binary encoding of the De Morgan dual of the CNF formula decoded from $x$, regarded as a DNF formula.

**Proof.** Use the syntax-recognition result to relate acceptance of $x$ to whether parsing succeeds, and split on the parser result. If parsing fails, syntax recognition implies that the scanner does not end in the exact-end state. The guarded output is therefore the single bit $0$; decoding uses the empty fallback CNF, whose dual encodes as that same output. If parsing succeeds with formula $\varphi$, syntax recognition says the scan ends in the exact-end state, so the guarded output is the full scan of $x$. The parser representation theorem identifies $x$ with the serialization of $\varphi$. The serialization-dual identity then identifies its scan with the serialization of the dual of $\varphi$. Since decoding returns $\varphi$ in this case, this is the desired identity.

**Key facts.** `Complexity.taut_syntax_parse`, `Std.Sat.CNF.parse_repr`, `Complexity.tautDual_serialize`.
