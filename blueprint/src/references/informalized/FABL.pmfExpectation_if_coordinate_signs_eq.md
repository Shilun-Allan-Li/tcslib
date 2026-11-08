<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/RegularThresholdNoiseStability.lean :: FABL.pmfExpectation_if_coordinate_signs_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Agreement Probability in a Correlated Sign Pair

**Claim.** For a coordinate of a correlated sign pair with parameter $\rho$, the expectation of the function that takes value $u$ when the signs agree and $v$ otherwise is $\frac{1+\rho}{2}u+\frac{1-\rho}{2}v$.

**Proof.** First express the agreement indicator in terms of the product of the two signs: since each sign is either $-1$ or $1$, the function is identically $\frac{u+v}{2}+\frac{u-v}{2}X_iY_i$, where $X_i$ and $Y_i$ are the signs in coordinate $i$. Indeed, their product is $1$ when they agree and $-1$ when they disagree. The correlated-pair expectation of this sign product is $\rho$ (\texttt{FABL.correlatedPairPMF\_expect\_signValue\_mul}). Linearity of expectation, together with the fact that the expectation of a constant is that constant and constants factor out of expectation (\texttt{FABL.pmfExpectation\_add}, \texttt{FABL.pmfExpectation\_const}, and \texttt{FABL.pmfExpectation\_const\_mul}), therefore gives $\frac{u+v}{2}+\frac{u-v}{2}\rho$. Rearranging yields the claimed expression.

**Key facts.** `FABL.correlatedPairPMF_expect_signValue_mul`, `FABL.pmfExpectation_add`, `FABL.pmfExpectation_const`, `FABL.pmfExpectation_const_mul`.
