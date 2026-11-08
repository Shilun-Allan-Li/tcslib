<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/MathlibBridge.lean :: Turing.CodeFormat.exists_canonizer -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Finite-Time Serialization Machine

**Claim.** If the table-skipping function of $F$ is primitive recursive, there exist a finite Turing machine $M$ and a time bound $T$ such that on every bit string $x$, $M$ halts within $T(|x|)$ steps and outputs the serialization of the code obtained by decoding $x$.

**Proof.** The primitive-recursiveness of the table-skipping function implies that the canonicalization function of $F$ is primitive recursive (`Turing.CodeFormat.primrec_canonical`). The general machine-realization theorem for primitive-recursive functions then supplies a finite Turing machine and a time bound computing this canonicalization on every input (`Turing.codePrim_machine`). By the canonical-code identity, canonicalization of $x$ equals the serialization of the code decoded from $x$ (`Turing.CodeFormat.canonical_eq`). Thus the supplied machine and bound have the required output and halting-time property.

**Key facts.** `Turing.CodeFormat.primrec_canonical`, `Turing.codePrim_machine`, `Turing.CodeFormat.canonical_eq`.
