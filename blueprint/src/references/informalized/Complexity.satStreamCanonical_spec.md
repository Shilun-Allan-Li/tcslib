<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satStreamCanonical_spec -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Canonicalization and decoding

**Claim.** For every finite binary string $x$, its canonicalization is the serialization of the CNF formula obtained by decoding $x$.

**Proof.** Split according to whether parsing $x$ succeeds. If parsing fails, the syntax characterization says that $x$ is not syntactically valid. Canonicalization therefore returns the fallback word $[\mathrm{false}]$; decoding also returns the empty fallback formula, whose serialization is exactly that word. If parsing succeeds with formula $\varphi$, the parser representation theorem identifies $x$ with the serialization of $\varphi$. The parse/serialize theorem then ensures that this serialization is syntactically valid, so canonicalization leaves $x$ unchanged. Decoding returns $\varphi$, and hence its serialization is again $x$.

**Key facts.** `Std.Sat.CNF.syntaxOK_spec`, `Std.Sat.CNF.parse_repr`, `Std.Sat.CNF.parse_serialize`.
