<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/ProductHypercontractivity.lean :: FABL.pmfCouplingInner_correlatedSignPair_split -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coupling Identity via Noise Operators

**Claim.** When $ab=\rho$, the correlated coupling expectation equals the uniform inner product of the two noise-smoothed functions, $\langle T_a f,T_b g\rangle$.

**Proof.** First use the correlated sign coupling identity (\texttt{pmfCouplingInner_correlatedSignPair}) to write the left side as $f_{\mathrm e}g_{\mathrm e}+\rho f_{\mathrm o}g_{\mathrm o}$. By the definition of the noise operator, its two inputs are $f_{\mathrm e}+a f_{\mathrm o}x$ and $g_{\mathrm e}+b g_{\mathrm o}x$. Their uniform inner product is the average of their product over the two signs. Expanding, the terms linear in $x$ average to zero and $x^2$ averages to one, leaving $f_{\mathrm e}g_{\mathrm e}+ab f_{\mathrm o}g_{\mathrm o}$. The hypothesis $ab=\rho$ identifies this with the coupling expression.

**Key facts.** `FABL.pmfCouplingInner_correlatedSignPair`.
