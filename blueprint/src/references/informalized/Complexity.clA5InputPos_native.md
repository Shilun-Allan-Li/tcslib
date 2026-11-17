<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clA5InputPos_native -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Stored Input Position

**Claim.** If the unary encoding of a time function is polynomial-time computable, then so is the unary encoding of the stored input position at that time.

**Proof.** The stored input position is the first trajectory count plus one, minus the second trajectory count. Each count, evaluated at the given time function, has a polynomial-time computable unary encoding (`clA5Count_native`); the required coordinate indices are fixed by the machine. Adding the two unary values and the constant one preserves polynomial-time computability (`clA5Add_native`, `clA5_pt_const`). Subtracting the second count then gives the unary encoding of the stored position (`clA5Sub_native`).

**Key facts.** `Complexity.clA5Count_native`, `Complexity.clA5Add_native`, `Complexity.clA5_pt_const`, `Complexity.clA5Sub_native`.
