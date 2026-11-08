<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/NP.lean :: Complexity.certificateSplit_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# No certificate split at zero

**Claim.** For all $C,c\in\mathbb{N}$, the certificate split at length zero is undefined.

**Proof.** Suppose the search at length zero returned some $n$. Its specification (`Complexity.certificateSplit_spec`) would give $n+(C+1)(n+1)^c=0$. But the marker-room inequality (`Complexity.certificate_room`) implies $(C+1)(n+1)^c\ge C(n+1)^c+1$, so the left side is positive. This contradicts its being zero; hence the search returns no result.

**Key facts.** `Complexity.certificateSplit_spec`, `Complexity.certificate_room`.
