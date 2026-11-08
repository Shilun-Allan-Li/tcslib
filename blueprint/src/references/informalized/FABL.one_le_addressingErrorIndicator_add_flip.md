<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/FriedgutNecessity.lean :: FABL.one_le_addressingErrorIndicator_add_flip -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Addressing error under a selected-coordinate flip

**Claim.** If the address-selected coordinate lies outside the coordinates on which $g$ depends, then the two error indicators, before and after flipping that coordinate, sum to at least $1$.

**Proof.** Flipping the address-selected coordinate negates the addressing function's output (`addressingFunction_flip_selected`), while leaving $g$ unchanged because its selected coordinate is outside its dependence set (`eq_addressingFlip_of_dependsOn`). If the two functions agree at the original input, then the original error is zero and the flipped outputs differ: a sign in $\{−1,1\}$ cannot equal its own negation. Thus the flipped error indicator is one. If they disagree originally, the first error indicator is already one. In either case the sum is at least one. The flip map's defining formula (`addressingFlipEquiv_apply`) identifies the transformed input with this selected-coordinate flip.

**Key facts.** `FABL.addressingFlipEquiv_apply`, `FABL.addressingFunction_flip_selected`, `FABL.eq_addressingFlip_of_dependsOn`.
