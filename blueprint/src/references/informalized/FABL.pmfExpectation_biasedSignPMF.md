<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedAnalysis.lean :: FABL.pmfExpectation_biasedSignPMF -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expectation under a Biased Sign Distribution

**Claim.** For $p\in(0,1)$, the expectation of a real-valued function $g$ under the sign distribution assigning probabilities $1-p$ to $1$ and $p$ to $-1$ is $(1-p)g(1)+pg(-1)$.

**Proof.** The sign set has exactly the two elements $1$ and $-1$, so the defining finite sum for expectation has just these two terms. The probability assigned to a sign $x$ is $1-p$ when $x=1$ and $p$ otherwise (\texttt{FABL.biasedSignPMF\_apply\_toReal}). Evaluating the two terms gives $(1-p)g(1)+pg(-1)$.

**Key facts.** `FABL.biasedSignPMF_apply_toReal`.
