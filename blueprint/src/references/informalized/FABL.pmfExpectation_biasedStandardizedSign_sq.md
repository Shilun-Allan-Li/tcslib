<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedAnalysis.lean :: FABL.pmfExpectation_biasedStandardizedSign_sq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Standardized sign second moment

**Claim.** For a sign chosen with mean $1-2p$, the standardized sign $Z$ has second moment $1$.

**Proof.** The sign takes only the values $1$ and $-1$, so its expectation is a sum over those two outcomes. Their probabilities are respectively $1-p$ and $p$ (the probability formula is `FABL.biasedSignPMF_apply_toReal`), and their sign values are $1$ and $-1$ (`FABL.signValue_one`, `FABL.signValue_neg_one`). Substituting these values into $Z=(X-(1-2p))/\sigma$ reduces the expectation of $Z^2$ to the two corresponding weighted squares. Since $\sigma^2=4p(1-p)$ (`FABL.biasSigma_sq`), the resulting numerator simplifies to $4p(1-p)$, and division by this positive quantity gives $1$. Positivity follows from $0<p<1$, which also ensures the denominators are nonzero.

**Key facts.** `FABL.biasedSignPMF_apply_toReal`, `FABL.signValue_one`, `FABL.signValue_neg_one`, `FABL.biasSigma_pos`, `FABL.biasSigma_sq`.
