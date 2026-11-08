<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CertShell.lean :: Turing.certSplit_valid -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Validity of the Certificate Split

**Claim.** If the split solver returns $i$, then the suffix of $y$ after its first $i$ bits has length $C$ times one plus the length of that prefix, raised to the power $c$.

**Proof.** A returned index from the list search belongs to the search range and satisfies its Boolean test. The range condition gives $i\le |y|$, while the successful test gives $i+C(i+1)^c=|y|$. Because $i\le |y|$, the prefix of length $i$ has length $i$; the suffix length is $|y|-i$. Substituting the search equation yields the claimed suffix-length formula.
