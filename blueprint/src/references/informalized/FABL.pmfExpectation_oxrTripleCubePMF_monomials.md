<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/HastadThreeSat.lean :: FABL.pmfExpectation_oxrTripleCubePMF_monomials -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expectation of a product of three monomials

**Claim.** For finite index sets $A,B,C\subseteq[n]$, the expectation of the product of their monomials on the three query vectors is zero unless $B=C$ and $A\subseteq B$. When these conditions hold, it equals $(-(1-\delta))^{|A|}(-\delta)^{|B|-|A|}$.

**Proof.** First factor the integrand coordinatewise. For each coordinate $i$, include its sign from query 0, 1, or 2 exactly when $i$ belongs to $A$, $B$, or $C$, respectively; the product over all coordinates is the original product of monomials. Since the coordinates are independent, the expectation of this product is the product of the coordinatewise expectations (`pmfExpectation_independentProductPMF_prod`). The selected-sign formula for one mixed triple (`pmfExpectation_oxrCoordinateTriplePMF_selectedSign`) gives each such factor. If $B\ne C$, there is a coordinate in exactly one of these sets, so its factor is zero and the whole product vanishes. If $B=C$ but $A\not\subseteq B$, some coordinate lies in $A$ but not $B$, again giving a zero factor. In the remaining case, coordinates in $A$ contribute $-(1-\delta)$, those in $B\setminus A$ contribute $-\delta$, and those outside $B$ contribute $1$. Multiplying these contributions gives the stated powers; the product over the two nested sets is exactly the corresponding cardinality powers (`prod_piecewise_two_sets`).

**Key facts.** `FABL.pmfExpectation_independentProductPMF_prod`, `FABL.pmfExpectation_oxrCoordinateTriplePMF_selectedSign`, `FABL.prod_piecewise_two_sets`.

**Caveat.** The payload's informal statement describes an acceptance-probability calculation, but the supplied formal statement and proof establish the monomial expectation identity stated here.
