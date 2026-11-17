<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Parity.lean :: FABL.parityCNF_toBooleanFunction -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Parity CNF represents parity

**Claim.** For every natural number $n$, the Boolean function represented by the CNF formed from the minterm DNF of the dual of parity equals parity on all $n$ coordinates.

**Proof.** Apply injectivity of the Boolean dual (FABL.CNFFormula.booleanDual_injective): it suffices to show that the duals of the two functions in the claim agree. The switch-and-OR transformation has represented function equal to the Boolean dual of the original CNF's represented function (FABL.CNFFormula.switchAndOr_toBooleanFunction). Thus the required equality of duals reduces to saying that the minterm DNF of the dual of parity represents that dual function. This is precisely the representation property of minterm DNF (FABL.mintermDNF_toBooleanFunction), completing the argument.

**Key facts.** `FABL.CNFFormula.booleanDual_injective`, `FABL.CNFFormula.switchAndOr_toBooleanFunction`, `FABL.mintermDNF_toBooleanFunction`.
