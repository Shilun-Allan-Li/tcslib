<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/HastadThreeSat.lean :: FABL.oxrPredicate_randomizedValue -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Randomized predicate value

**Claim.** For means $[?]$ (that is, $[?]$) $[?]$—specifically, for $[?]$; more simply, for the three means $[?]$—the randomized acceptance probability is $\frac34-\frac{\mu_0}{4}-\frac{\mu_1\mu_2}{4}-\frac{\mu_0\mu_1\mu_2}{4}$.

**Proof.** Write $Y=(Y_0,Y_1,Y_2)$ for the three independent random signs, with $\mathbb E[Y_i]=\mu_i$. The indicator of acceptance is the polynomial $\frac34-\frac14Y_0-\frac14Y_1Y_2-\frac14Y_0Y_1Y_2$ (the predicate's indicator identity, `FABL.oxrPredicate_indicator_eq`). Taking expectations term by term is valid by additivity of expectation and its behavior on constants and constant multiples (`FABL.pmfExpectation_add`, `FABL.pmfExpectation_const`, `FABL.pmfExpectation_const_mul`). For each product of coordinates, independence factors its expectation into the product of the individual means (`FABL.pmfExpectation_independentProduct_subsetProd`); each coordinate has mean $\mu_i$ (`FABL.pmfExpectation_signPMFOfMean`). Thus the three nonconstant terms have expectations $\mu_0$, $\mu_1\mu_2$, and $\mu_0\mu_1\mu_2$, respectively, giving the claimed formula.

**Key facts.** `FABL.oxrPredicate_indicator_eq`, `FABL.pmfExpectation_add`, `FABL.pmfExpectation_const`, `FABL.pmfExpectation_const_mul`, `FABL.pmfExpectation_independentProduct_subsetProd`, `FABL.pmfExpectation_signPMFOfMean`.
