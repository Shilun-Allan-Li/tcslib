<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/KushilevitzMansour.lean :: FABL.card_l1ConcentratingFourierFamily_le_familySizeBound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier family size bound

**Claim.** If the Fourier $1$-norm of the real-valued target is at most $s$, then the number of subsets whose Fourier coefficient magnitude, multiplied by that norm, is at least $\varepsilon/4$ is at most the stated family-size bound.

**Proof.** The parameter satisfies $0<\varepsilon\leq 1/2$ (\(\texttt{positiveLearningParameter\_toReal\_mem\_Ioc}\)), so $\varepsilon/4>0$. Apply the concentrating-family bound (\(\texttt{card\_l1ConcentratingFourierFamily\_le}\)) at threshold $\varepsilon/4$: the real cardinality is at most $\|\widehat f\|_1^2/(\varepsilon/4)=4\|\widehat f\|_1^2/\varepsilon$. The norm is nonnegative by \(\texttt{fourierOneNorm\_nonneg}\); together with the assumed upper bound by $s$, this implies $\|\widehat f\|_1^2\leq s^2$. Since $\varepsilon>0$, the cardinality is thus at most $4s^2/\varepsilon$, and hence at most its ceiling. Converting the real inequality to natural cardinalities gives the bound by that ceiling, which is no larger than the maximum of the ceiling and $1$ appearing in the definition.

**Key facts.** `FABL.positiveLearningParameter_toReal_mem_Ioc`, `FABL.fourierOneNorm_nonneg`, `FABL.card_l1ConcentratingFourierFamily_le`.
