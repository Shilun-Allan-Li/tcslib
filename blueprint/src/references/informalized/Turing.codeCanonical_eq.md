<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeFormat.lean :: Turing.codeCanonical_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Canonical code of the decoded machine

**Claim.** For every Boolean string, its canonical code is the serialization of the machine obtained by decoding that string.

**Proof.** This is the specialization of the general canonicalization theorem for a code format (`CodeFormat.canonical_eq`) to the one-tape format. That theorem identifies a format’s canonical string with the serialization of the result of decoding the string; the definitions of `codeCanonical` and `codeDecode` are exactly the one-tape format’s canonicalization and decoding.

**Key facts.** `Turing.CodeFormat.canonical_eq`.
