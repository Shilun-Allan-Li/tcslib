<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/CircuitInfluence.lean :: FABL.CircuitGate.exists_eq_const_of_hasWidthLE_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Width-Zero Functions Are Constant

**Claim.** If a Boolean function has width at most zero in the normal form associated with an AND or OR gate, then it is constant.

**Proof.** Choose the cube point $x_0$ whose coordinates are all $1$, and use it to specify the constant value. If the gate is OR, the width hypothesis gives a DNF formula representing the function with width zero. The width is therefore exactly zero, and the fact that a width-zero DNF has the same value at any two inputs (`FABL.DNFFormula.toBooleanFunction_eq_of_width_eq_zero`) shows that the represented function agrees with its value at $x_0$ everywhere. If the gate is AND, convert the CNF formula to a DNF formula by switching AND and OR. This conversion preserves zero width, so the resulting DNF has equal values at the coordinatewise negations of any two inputs. Its represented function is the Boolean dual of the original function (`FABL.CNFFormula.switchAndOr_toBooleanFunction`). Applying the width-zero DNF fact to the negations of $x$ and $x_0$, then undoing Boolean duality, shows that the original function has equal values at $x$ and $x_0$. Thus in either case it is constant.

**Key facts.** `FABL.DNFFormula.toBooleanFunction_eq_of_width_eq_zero`, `FABL.CNFFormula.switchAndOr_toBooleanFunction`.
