<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/UpperBounds.lean :: CommunicationComplexity.Deterministic.communicationComplexity_le_clog_card_Y_alpha -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input and Output Upper Bound

**Claim.** For finite nonempty $Y$ and $\alpha$, and arbitrary $X$, the deterministic communication complexity of $f:X\to Y\to\alpha$ is at most $\lceil\log_2|Y|\rceil+\lceil\log_2|\alpha|\rceil$.

**Proof.** Bob first sends his input $y$. Alice then knows $y$ and her own input $x$, so she sends the value $f(x,y)$, which the protocol outputs. These messages use alphabets of sizes $|Y|$ and $|\alpha|$, and hence have total cost $\lceil\log_2|Y|\rceil+\lceil\log_2|\alpha|\rceil$. Applying the fact that any protocol computing $f$ bounds its deterministic communication complexity from above (\texttt{communicationComplexity\_le\_of\_finiteMessage\_protocol}) proves the claim.

**Key facts.** `CommunicationComplexity.Deterministic.communicationComplexity_le_of_finiteMessage_protocol`.
