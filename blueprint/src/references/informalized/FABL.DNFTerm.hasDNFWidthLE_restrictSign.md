<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/CircuitInfluence.lean :: FABL.DNFTerm.hasDNFWidthLE_restrictSign -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# DNF Width After Restriction

**Claim.** The restriction of the function represented by $T$ has a DNF representation of width at most the restricted width of $T$ under $\rho$.

**Proof.** Take the restriction formula associated with $T$ and $\rho$. Its represented Boolean function is exactly the restriction of the function represented by $T$ (\texttt{restrictionFormula\_toBooleanFunction}). Its width equals the restricted width of $T$ (\texttt{width\_restrictionFormula}), and therefore is in particular at most that bound. This formula witnesses the required representation.

**Key facts.** `FABL.DNFTerm.width_restrictionFormula`, `FABL.DNFTerm.restrictionFormula_toBooleanFunction`.
