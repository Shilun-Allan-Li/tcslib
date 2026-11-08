<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/CorrelatedMajority.lean :: FABL.normalizedCorrelatedPairSum_projection_secondMoment -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Second Moment of a Linear Projection

**Claim.** The expected square of the inner product of the normalized pair sum with $t=(t_1,t_2)$ equals $t_1^2+2\rho t_1t_2+t_2^2$.

**Proof.** Expand the squared inner product into the first coordinate squared times $t_1^2$, twice the product of the two coordinates times $t_1t_2$, and the second coordinate squared times $t_2^2$. By linearity of expectation and the ability to pull out constants (\texttt{FABL.pmfExpectation_add}, \texttt{FABL.pmfExpectation_mul_const}, and \texttt{FABL.pmfExpectation_const_mul}), the expectation is the same combination of the corresponding moments. The first and second coordinate second moments are each $1$ (\texttt{FABL.normalizedCorrelatedPairSum_first_secondMoment} and \texttt{FABL.normalizedCorrelatedPairSum_second_secondMoment}), while their cross moment is $\rho$ (\texttt{FABL.normalizedCorrelatedPairSum_crossMoment}). Substituting these values gives $t_1^2+2\rho t_1t_2+t_2^2$.

**Key facts.** `FABL.normalizedCorrelatedPairSum_first_secondMoment`, `FABL.normalizedCorrelatedPairSum_second_secondMoment`, `FABL.normalizedCorrelatedPairSum_crossMoment`, `FABL.pmfExpectation_add`, `FABL.pmfExpectation_mul_const`, `FABL.pmfExpectation_const_mul`.
