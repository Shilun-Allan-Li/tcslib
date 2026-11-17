<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/HastadThreeSat.lean :: FABL.pmfExpectation_oxrTripleCubePMF_tripleProduct_eq_randomSubsetAverage -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Triple Product as a Subset Average

**Claim.** For odd $f$, the expectation of the product of its values on the three query vectors is the sum over $S$ of $\widehat f(S)^2$ times the stated random-subset Fourier average.

**Proof.** First use the Fourier expansion of the triple-product expectation (`pmfExpectation_oxrTripleCubePMF_tripleProduct_fourier`), which writes it as a sum over $S$ of $\widehat f(S)^2$ times a weighted sum over subsets $J\subseteq S$. The oddness hypothesis is used in the identity `oxrTripleFourierTerm_eq_randomSubsetAverage_of_odd`: it identifies that weighted sum with the average obtained by choosing a subset $K$ with the specified weights, intersecting it with $S$, and evaluating $(-1)^{|S\cap K|}\widehat f(S\cap K)$. Apply this identity term by term in the outer sum to obtain the claimed expression.

**Key facts.** `FABL.pmfExpectation_oxrTripleCubePMF_tripleProduct_fourier`, `FABL.oxrTripleFourierTerm_eq_randomSubsetAverage_of_odd`.
