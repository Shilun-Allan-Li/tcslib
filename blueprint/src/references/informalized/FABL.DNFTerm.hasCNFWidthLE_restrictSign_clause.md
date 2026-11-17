<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/CircuitInfluence.lean :: FABL.DNFTerm.hasCNFWidthLE_restrictSign_clause -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# CNF Width After Restricting a Clause

**Claim.** The restriction of the clause represented by $T$ has a CNF representation whose width is at most the restricted width of $T$, computed after negating the fixed signs of the restriction.

**Proof.** Regard the clause represented by $T$ as the Boolean dual of the function represented by the conjunction $T$ (\texttt{CNFFormula.clauseEval\_eq\_booleanDual\_eval}). Restricting a Boolean dual is the same as taking the Boolean dual after restricting the original function, provided the restriction's fixed states are negated (\texttt{CoordRestriction.restrictSign\_booleanDual}). The restricted conjunction has a DNF representation of width at most its restricted width under this negated restriction (\texttt{DNFTerm.hasDNFWidthLE\_restrictSign}). Taking the Boolean dual of that representation produces a CNF representation with the same width bound (\texttt{HasDNFWidthLE.booleanDual}). Together these identities give the stated bound for the restricted clause.

**Key facts.** `FABL.CNFFormula.clauseEval_eq_booleanDual_eval`, `FABL.CoordRestriction.restrictSign_booleanDual`, `FABL.DNFTerm.hasDNFWidthLE_restrictSign`, `FABL.HasDNFWidthLE.booleanDual`.
