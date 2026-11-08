<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeFormat.lean :: Turing.CodeFormat.canonical_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Canonical Code from Decoding

**Claim.** For every code format $F$ and Boolean word $xs$, the canonical form of $xs$ equals the serialization of the code obtained by decoding $xs$.

**Proof.** By the scan characterization, scanning $xs$ returns the tail from full parsing when full parsing succeeds, and reports failure otherwise (`Turing.CodeFormat.scan_full`). If full parsing fails, both the canonical form and the decoded code use the format's fallback, so the equality follows from the definition of serialization of that decoded code. If parsing succeeds with code $M$ and tail $t$, parse soundness gives $xs=F.serialize(M)++t$ (`Turing.CodeFormat.parseFull_sound`). The canonical form takes the prefix of $xs$ obtained by removing the length of $t$, which is exactly $F.serialize(M)$. In this successful case decoding returns $M$, so this prefix is the serialization of the decoded code.

**Key facts.** `Turing.CodeFormat.scan_full`, `Turing.CodeFormat.parseFull_sound`.
