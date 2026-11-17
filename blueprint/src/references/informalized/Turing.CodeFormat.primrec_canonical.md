<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/MathlibBridge.lean :: Turing.CodeFormat.primrec_canonical -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Primitive Recursiveness of Canonicalization

**Claim.** If the table-skipping function of $F$ is primitive recursive, then canonicalization of bit strings for $F$ is primitive recursive.

**Proof.** The scan function is primitive recursive under the assumed primitive recursiveness of table skipping (`Turing.CodeFormat.primrec_scan`). Canonicalization branches on the scan result: if scanning fails, it returns the fixed serialization of the fallback code; if scanning succeeds with remainder $u$, it returns the input with its final $|u|$ bits removed. The first branch is primitive recursive because it is constant. In the second branch, list length and the operation that takes an input list and a length and returns that many initial bits after subtracting the length from the input length are primitive recursive (`Turing.codePrimPrefix`). Primitive-recursive case analysis on the scan result therefore gives primitive recursiveness of canonicalization.

**Key facts.** `Turing.CodeFormat.primrec_scan`, `Turing.codePrimPrefix`.
