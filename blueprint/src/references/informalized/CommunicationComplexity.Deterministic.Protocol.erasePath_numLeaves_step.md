<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/Subprotocol.lean :: CommunicationComplexity.Deterministic.Protocol.erasePath_numLeaves_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Leaf Count Identity for Erasure

**Claim.** If the selected branch has $e=\ell(P(b))-\ell(s)+1$ leaves after erasure, replacing that branch's count in the two-branch sum gives $\ell(P(\mathrm{false}))+\ell(P(\mathrm{true}))-\ell(s)+1$.

**Proof.** The subprotocol path ensures $\ell(s)\le\ell(P(b))$ (`SubprotocolPath.numLeaves_le`). Thus the truncated difference in the selected branch is an ordinary nonnegative difference. For $b=\mathrm{false}$, substitute $e=\ell(P(\mathrm{false}))-\ell(s)+1$ into $e+\ell(P(\mathrm{true}))$; for $b=\mathrm{true}$, substitute it into $\ell(P(\mathrm{false}))+e$. In both cases, elementary arithmetic gives the sum of the two original branch counts minus $\ell(s)$, plus one.

**Key facts.** `CommunicationComplexity.Deterministic.Protocol.SubprotocolPath.numLeaves_le`.
