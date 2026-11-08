<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/FriedgutNecessity.lean :: FABL.addressingInputEquiv_first_flip_selected -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Address Preservation Under a Selected Flip

**Claim.** For every natural number $m$ and sign vector $x$ of length $m+2^m$, flipping the coordinate selected by the address encoded by the first component leaves that first component unchanged.

**Proof.** To compare the first components, evaluate them at an arbitrary address coordinate $i\in\mathrm{Fin}(m)$. The address-coordinate formula identifies this value with the original vector's value at the coordinate corresponding to the left summand element $i$. The selected coordinate, by definition, corresponds to an element of the right summand. These coordinates are distinct: applying the injectivity of the sum-coordinate equivalence to an assumed equality would identify a left summand element with a right summand element, which is impossible. A flip therefore leaves the value at the address coordinate unchanged. Since this holds for every $i$, the first components agree.

**Key facts.** `FABL.addressingInputEquiv_addressCoordinate`, `FABL.setCoordinate_apply_of_ne`.
