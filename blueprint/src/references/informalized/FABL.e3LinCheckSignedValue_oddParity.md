<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/HastadLimitations.lean :: FABL.e3LinCheckSignedValue_oddParity -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Odd parity factorization

**Claim.** For an odd number $2k+1$ of coordinates, the signed value of an E3 linearity check on the full parity function is the product of its signed values on all dictator functions.

**Proof.** Since the check predicate belongs to the specified family, choose a sign $b$ for which it is the three-variable linearity predicate with right-hand side $b$. The signed-value formula for that predicate expresses the value on any Boolean function as $b$ times the product of its three queried outputs (`FABL.e3LinCheckSignedValue_eq`). The full parity function has real-valued output equal to the monomial over all coordinates (`FABL.parityFunction_toReal`), while each dictator has real-valued output equal to the monomial on its singleton coordinate (`FABL.dictator_toReal_eq_monomial_singleton`). Expanding these products and rearranging the finite products shows that the only discrepancy between the parity value and the product of the dictator values is the factor $b$ appearing once on the left and once for each of the $2k+1$ dictators on the right. Because this count is odd, these factors agree: for either possible sign $b$, $b^{2k+1}=b$. Thus the two signed values have the asserted product relation.

**Key facts.** `FABL.e3LinCheckSignedValue_eq`, `FABL.parityFunction_toReal`, `FABL.dictator_toReal_eq_monomial_singleton`.
