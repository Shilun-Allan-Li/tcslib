<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/CircuitInfluence.lean :: FABL.DepthCircuit.layer1Function_hasWidthLE_extendedSignRestriction_max -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Restricted first-layer width bound

**Claim.** After fixing coordinates outside $J$ according to $z$, the restricted function of a first-layer gate has the representation type specified by the dual gate, with width at most the maximum restricted width among the first-layer gates.

**Proof.** Fix the coordinate restriction induced by $J$ and $z$. The selected gate’s restricted width is at most the maximum restricted width over all first-layer gates (`layer1RestrictedWidth_le_max`). The restricted gate-width representation theorem gives the restricted function of that gate a representation of the required type with width bounded by its own restricted width (`CircuitGate.hasWidthLE_restrictSign_evalTerm`). The restriction induced by $J$ and $z$ agrees with the stated extension of the function (`CoordRestriction.restrictSign_coordRestrictionOf`). Finally, the function of the selected first-layer gate is its stored term evaluated with the circuit’s gate type; applying the representation theorem to that term and then enlarging the width bound using the preceding maximum inequality proves the result (`CircuitGate.hasWidthLE_mono`).

**Key facts.** `FABL.DepthCircuit.layer1RestrictedWidth_le_max`, `FABL.CircuitGate.hasWidthLE_mono`, `FABL.CoordRestriction.restrictSign_coordRestrictionOf`, `FABL.CircuitGate.hasWidthLE_restrictSign_evalTerm`.
