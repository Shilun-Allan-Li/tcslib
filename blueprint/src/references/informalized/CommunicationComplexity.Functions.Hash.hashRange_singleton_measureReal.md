<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncHash.lean :: CommunicationComplexity.Functions.Hash.hashRange_singleton_measureReal -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Real singleton measure

**Claim.** Under the uniform volume measure on $\mathrm{Fin}\,k$, the real-valued measure of each singleton is $1/k$.

**Proof.** The real-valued measure is obtained by taking the real value of the extended measure. The singleton has extended measure $1/k$ by the singleton-measure result (\texttt{hashRange\_singleton\_measure}); converting this finite value to a real gives $1/k$.

**Key facts.** `CommunicationComplexity.Functions.Hash.hashRange_singleton_measure`.
