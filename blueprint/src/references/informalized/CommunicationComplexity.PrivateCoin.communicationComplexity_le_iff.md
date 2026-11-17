<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/PrivateCoinComplexity.lean :: CommunicationComplexity.PrivateCoin.communicationComplexity_le_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Upper-bound characterization

**Claim.** The private-coin randomized communication complexity of $f$ is at most $n$ exactly when there are coin-tape lengths and a protocol on those tapes that computes $f$ with error at most $\varepsilon$ on every input and has communication cost at most $n$.

**Proof.** Unfold the complexity as the iterated infimum over Alice's tape length, Bob's tape length, protocols, and error-validity witnesses. The extended-natural infimum characterization says that an infimum is at most the natural number $n$ exactly when some index has value at most $n$ (\texttt{CommunicationComplexity.Internal.enat\_iInf\_le\_coe\_iff}). Here an index consists of the two tape lengths, a protocol, and a proof that it meets the error bound; the indexed value is that protocol's cost. Reordering these existential data gives precisely the stated characterization.

**Key facts.** `CommunicationComplexity.Internal.enat_iInf_le_coe_iff`.
