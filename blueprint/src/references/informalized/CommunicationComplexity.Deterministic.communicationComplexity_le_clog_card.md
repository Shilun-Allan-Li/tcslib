<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/UpperBounds.lean :: CommunicationComplexity.Deterministic.communicationComplexity_le_clog_card -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input-Size Upper Bound

**Claim.** For finite nonempty input types $X$ and $Y$, the deterministic communication complexity of any function $f:X\to Y\to\alpha$ is at most $\lceil\log_2|X|\rceil+\lceil\log_2|Y|\rceil$.

**Proof.** Give Alice the task of sending her input $x$ as a message, then give Bob the task of sending his input $y$; the protocol outputs $f(x,y)$. With finite alphabets, transmitting an element of an alphabet of size $m$ costs $\lceil\log_2m\rceil$ bits, so this protocol has cost exactly the sum of the two stated bounds. Since a protocol computing $f$ with cost at most $c$ implies $D(f)\le c$ (\texttt{communicationComplexity\_le\_of\_finiteMessage\_protocol}), the result follows.

**Key facts.** `CommunicationComplexity.Deterministic.communicationComplexity_le_of_finiteMessage_protocol`.
