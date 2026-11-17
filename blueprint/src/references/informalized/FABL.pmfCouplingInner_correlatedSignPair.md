<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/ProductHypercontractivity.lean :: FABL.pmfCouplingInner_correlatedSignPair -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Correlated Sign Coupling Identity

**Claim.** For the correlated pair $(X,Y)$, the expectation of $f(X)g(Y)$ equals $f_{\mathrm e}g_{\mathrm e}+\rho f_{\mathrm o}g_{\mathrm o}$.

**Proof.** Write each function in its affine form on the two signs: $f(s)=f_{\mathrm e}+f_{\mathrm o}\,\mathrm{signValue}(s)$ and likewise for $g$. Multiplying these expressions gives a constant term, two terms linear in one coordinate, and a term proportional to the product of the two signs. Taking expectation, the constant term remains unchanged. The two linear terms vanish because each marginal sign has mean zero, by the first-coordinate and second-coordinate mean identities (\texttt{correlatedSignPairPMF_expect_signValue_fst} and \texttt{correlatedSignPairPMF_expect_signValue_snd}). The product term contributes the product of the odd coefficients times $\rho$, since the expected product of the signs is $\rho$ (\texttt{correlatedSignPairPMF_expect_signValue_mul}). Linearity of expectation and the fact that constants factor out (\texttt{pmfExpectation_add}, \texttt{pmfExpectation_const}, and \texttt{pmfExpectation_const_mul}) yield the stated formula.

**Key facts.** `FABL.sign_affine_reconstruct`, `FABL.pmfExpectation_add`, `FABL.pmfExpectation_const`, `FABL.pmfExpectation_const_mul`, `FABL.correlatedSignPairPMF_expect_signValue_snd`, `FABL.correlatedSignPairPMF_expect_signValue_fst`, `FABL.correlatedSignPairPMF_expect_signValue_mul`.
