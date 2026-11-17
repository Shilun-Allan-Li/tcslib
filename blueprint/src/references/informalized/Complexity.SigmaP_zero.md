<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/PolyHierarchy/Defs.lean :: Complexity.SigmaP_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zeroth Existential Level

**Claim.** The zeroth existential level equals polynomial time: $\Sigma_0^P=\mathsf{P}$.

**Proof.** By the zero-level characterization of the alternating classes, $\mathrm{altClass}(b,0)=\mathsf{P}$ for either choice of the quantifier flag ($\texttt{altClass_zero}$). Taking $b$ to be true and using $\Sigma_0^P=\mathrm{altClass}(\mathrm{true},0)$ gives the stated equality.

**Key facts.** `Complexity.altClass_zero`.
