<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/CircuitInfluence.lean :: FABL.CircuitGate.hasWidthLE_restrictSign_evalTerm -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Width of a restricted gate term

**Claim.** After restricting the function computed by a gate on a term of literals, the resulting function has a representation of width at most the term's restricted gate width in the dual normal form.

**Proof.** Split into the two gate choices. For an AND gate, the term computes its usual conjunction, and the dual representation is a DNF. The restricted term has a DNF of width at most its restricted width (`DNFTerm.hasDNFWidthLE_restrictSign`), which is exactly the restricted gate width in this case. For an OR gate, the term computes a clause, and the dual representation is a CNF. The restricted clause has a CNF of width at most the restricted width computed using the negated coordinate assignment (`DNFTerm.hasCNFWidthLE_restrictSign_clause`); that is the restricted gate width for OR. These two cases establish the claim.

**Key facts.** `FABL.DNFTerm.hasDNFWidthLE_restrictSign`, `FABL.DNFTerm.hasCNFWidthLE_restrictSign_clause`.
