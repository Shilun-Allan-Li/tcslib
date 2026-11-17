<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/FriedgutNecessity.lean :: FABL.eq_addressingFlip_of_dependsOn -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Addressing flip outside the dependence set

**Claim.** If the address-selected coordinate of x is outside J, then flipping that coordinate does not change g(x), provided g depends only on coordinates in J.

**Proof.** The dependence hypothesis says that two inputs agreeing at every coordinate in J have the same value under g. Compare x with the result of the addressing flip. At any coordinate i in J, the selected coordinate cannot equal i: otherwise the selected coordinate would belong to J, contrary to the hypothesis. Since updating a different coordinate leaves coordinate i unchanged, the two inputs agree throughout J. The dependence hypothesis therefore gives equality of their g-values.

**Key facts.** `FABL.addressingFlipEquiv_apply`, `FABL.setCoordinate_apply_of_ne`.
