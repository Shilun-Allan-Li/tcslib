<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/FriedgutNecessity.lean :: FABL.addressingInputEquiv_first_flip_data -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Data flip preserves address part

**Claim.** For every $m$, input $x$, and data index $j<2^m$, flipping coordinate $j$ leaves the address part of the decomposition of $x$ unchanged.

**Proof.** Compare the address parts coordinatewise. At each address index $i$, the decomposition reads the original input at its address coordinate (`FABL.addressingInputEquiv_addressCoordinate`). An address coordinate and a data coordinate are distinct, since they come from opposite summands of the disjoint union of coordinate positions. A flip at the data coordinate therefore leaves the input's address coordinate unchanged (`FABL.setCoordinate_apply_of_ne`). This holds for every address index, so the address parts agree.

**Key facts.** `FABL.addressingInputEquiv_addressCoordinate`, `FABL.setCoordinate_apply_of_ne`.
