<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/UpperBounds.lean :: CommunicationComplexity.Deterministic.communicationComplexity_le_clog_card_X_alpha -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input and Output Upper Bound

**Claim.** For finite nonempty $X$ and $\alpha$, and arbitrary $Y$, the deterministic communication complexity of $f:X\to Y\to\alpha$ is at most $\lceil\log_2|X|\rceil+\lceil\log_2|\alpha|\rceil$.

**Proof.** Use a protocol in which Alice sends her input $x$, after which Bob, who knows $x$ and his own input $y$, sends the value $f(x,y)$. The output is that value. The two messages have alphabet sizes $|X|$ and $|\alpha|$, so their costs are respectively $\lceil\log_2|X|\rceil$ and $\lceil\log_2|\alpha|\rceil$. The protocol-to-complexity upper bound (\texttt{communicationComplexity\_le\_of\_finiteMessage\_protocol}) gives the claimed inequality.

**Key facts.** `CommunicationComplexity.Deterministic.communicationComplexity_le_of_finiteMessage_protocol`.
