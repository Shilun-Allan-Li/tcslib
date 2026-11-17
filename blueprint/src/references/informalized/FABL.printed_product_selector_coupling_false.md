<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/ProductLTFNoise.lean :: FABL.printed_product_selector_coupling_false -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Disagreement of Two Couplings

**Claim.** The selector construction and the product resampling construction give different agreement probabilities: the first is $3/4$, while the second is $1/2$.

**Proof.** The selector construction has agreement probability $3/4$, by `printedSelectorAgreementAtZero_eq_three_fourths`. The independent product resampling construction has agreement probability $1/2$, by `productBoolAgreementAtZero_eq_one_half`. Since these rational numbers are unequal, the two probabilities differ.

**Key facts.** `FABL.printedSelectorAgreementAtZero_eq_three_fourths`, `FABL.productBoolAgreementAtZero_eq_one_half`.
