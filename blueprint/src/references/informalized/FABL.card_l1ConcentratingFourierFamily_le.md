<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/GoldreichLevin/RestrictedWeights.lean :: FABL.card_l1ConcentratingFourierFamily_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Size of a concentrating Fourier family

**Claim.** For a real-valued function on the Boolean cube and $\varepsilon>0$, the number of Fourier coefficients satisfying $\varepsilon\leq\|\widehat f\|_1|\widehat f(S)|$ is at most $\|\widehat f\|_1^2/\varepsilon$.

**Proof.** Write $\mathcal F$ for the family in question and $L=\|\widehat f\|_1$. Since $L$ is a sum of absolute values, it is nonnegative (\(\texttt{fourierOneNorm\_nonneg}\)). The sum of $|\widehat f(S)|$ over $S\in\mathcal F$ is at most the sum over all subsets, namely $L$, because every summand is nonnegative. For each $S\in\mathcal F$, the defining condition gives $\varepsilon\leq L|\widehat f(S)|$ (\(\texttt{mem\_l1ConcentratingFourierFamily}\)). Summing these inequalities over $\mathcal F$ yields $|\mathcal F|\varepsilon\leq L\sum_{S\in\mathcal F}|\widehat f(S)|\leq L^2$. Dividing by the positive $\varepsilon$ proves the stated bound.

**Key facts.** `FABL.fourierOneNorm_nonneg`, `FABL.mem_l1ConcentratingFourierFamily`.
