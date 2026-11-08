<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/DetComplexity.lean :: CommunicationComplexity.Deterministic.le_communicationComplexity_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Protocol Lower-Bound Characterization

**Claim.** For any function $f$ and natural number $n$, $n\le D(f)$ exactly when every deterministic protocol computing $f$ has complexity at least $n$.

**Proof.** By definition, $D(f)$ is the infimum of the costs of all protocols computing $f$. An element lies below this infimum exactly when it lies below every member of the family (the complete-lattice characterization of being below an infimum, here applied as $\texttt{le\_iInf\_iff}$). Taking that element to be $n$ yields the stated condition for every protocol, conditional on its computing $f$.
