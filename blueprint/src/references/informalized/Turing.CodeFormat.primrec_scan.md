<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/MathlibBridge.lean :: Turing.CodeFormat.primrec_scan -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Primitive Recursiveness of Scanning

**Claim.** If the table-skipping function of $F$ is primitive recursive, then the scan function of $F$ is primitive recursive.

**Proof.** Scan proceeds through a fixed sequence of primitive-recursive operations and conditional checks. First it decodes the pair, using the primitive-recursive pair decoder (`Turing.codePrimPair`); if decoding fails, scanning fails. From the decoded first component it computes the represented number and its binary representation, using the primitive-recursive number-value and binary-bit functions (`Turing.codePrimBitsNat`, `Turing.codePrimBits`). It rejects unless that representation agrees with the decoded bits, and then rejects unless the remaining suffix is long enough to meet the guard bound. It next skips the unary finite-state code, a primitive-recursive operation (`Turing.codePrimSkipFin`), then applies the assumed primitive-recursive table-skipping function. Finally, it returns the remaining suffix precisely when all its bits are $1$, a primitive-recursive test (`Turing.codePrimAll`); otherwise it fails. Composition, option binding, and conditional selection preserve primitive recursiveness, so the entire scan is primitive recursive.

**Key facts.** `Turing.codePrimPair`, `Turing.codePrimBitsNat`, `Turing.codePrimBits`, `Turing.codePrimSkipFin`, `Turing.codePrimAll`.
