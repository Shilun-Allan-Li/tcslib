<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/PCPPConstructions.lean :: FABL.arbitraryPropertyPCPPSystem_isPCPP -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# The Constructed PCPP Guarantee

**Claim.** The constructed verifier is a 3-query PCPP system for the property, with proof length $2^{2^n}$ and rejection rate $1/1000$.

**Proof.** Apply the general criterion that a verifier is a PCPP if it has positive rate, perfect completeness, and the required acceptance-to-closeness guarantee ($\texttt{isPCPP_of_exists_close_of_acceptanceProbability_ge}$). The proposed rate $1/1000$ is positive. For completeness, if $w$ satisfies the property, the encoded proof representing the dictator indexed by $w$ makes the verifier accept with probability $1$ ($\texttt{arbitraryPropertyPCPPSystem_complete}$). For soundness, the previously established closeness result says that acceptance at least $1-(1/1000)\varepsilon$ implies that $w$ is within distance $\varepsilon$ of a string satisfying the property ($\texttt{arbitraryPropertyPCPPSystem_close_of_acceptanceProbability_ge}$). These establish the three requirements of the criterion.

**Key facts.** `FABL.isPCPP_of_exists_close_of_acceptanceProbability_ge`, `FABL.arbitraryPropertyPCPPSystem_complete`, `FABL.arbitraryPropertyPCPPSystem_close_of_acceptanceProbability_ge`.
