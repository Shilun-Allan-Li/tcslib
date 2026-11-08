<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter01/FunctionsAsMultilinearPolynomials.lean :: FABL.monomial_granularityExtendAtOne -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monomial on a positive-sign extension

**Claim.** Extending an assignment on $J$ by $+1$ outside $J$, the monomial on $U$ equals the monomial on $U\cap J$ evaluated using the assignment on $J$.

**Proof.** First remove from the product over $U$ all coordinates outside $J$. At each such coordinate the extension has value $+1$, so its sign value is $1$ and removing that factor does not change the product. The resulting product is over $U\cap J$. Its factors correspond bijectively to the elements of the frequency set within $J$ (`mem_granularityFrequencyWithin`); for each such element, the extension agrees with the given assignment. Reindexing the product by this bijection gives the asserted monomial on the within-$J$ frequency set.

**Key facts.** `FABL.mem_granularityFrequencyWithin`.
