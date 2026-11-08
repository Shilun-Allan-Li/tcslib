<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satWidthScan_poly -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Width Scan

**Claim.** The function sending each Boolean word $x$ to the one-bit word containing its width-scan result is polynomial-time computable.

**Proof.** Use the finite-state scan machine with transition given by the width-pass update, initial state $(0,0,\mathrm{true})$, and acceptance test that reads the flag. The scan-machine computation theorem (`Complexity.satScan_computes`) says this machine outputs the acceptance value after $n+1$ steps on an input of length $n$. Here that value is precisely the width scan of $x$. Taking the polynomial bound with coefficient and exponent both equal to $1$ gives $1\cdot(n+1)^1=n+1$, as required.

**Key facts.** `Complexity.satScan_computes`.
