<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/OneWay.lean :: CommunicationComplexity.Deterministic.OneWay.deterministic_communicationComplexity_le_of_oneWay_le_bool -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Boolean One-Way Simulation Bound

**Claim.** If the one-way deterministic communication complexity of a Boolean-valued function is at most $n$, then its interactive deterministic communication complexity is at most $n+1$.

**Proof.** Apply the general one-way-to-interactive bound, which says that for outputs in a finite nonempty type $\alpha$, the interactive complexity is at most the one-way complexity plus $\mathrm{clog}_2(|\alpha|)$ (\texttt{deterministic\_communicationComplexity\_le\_of\_oneWay\_le}). For Boolean outputs, the codebook has size $2$, and $\mathrm{clog}_2(2)=1$ (\texttt{clog\_two\_two}). Substituting this value into the bound gives the claimed upper bound $n+1$.

**Key facts.** `CommunicationComplexity.Deterministic.OneWay.deterministic_communicationComplexity_le_of_oneWay_le`, `CommunicationComplexity.Deterministic.OneWay.clog_two_two`.
