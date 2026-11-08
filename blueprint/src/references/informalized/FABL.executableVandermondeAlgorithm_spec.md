<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/ExecutableVandermonde.lean :: FABL.executableVandermondeAlgorithm_spec -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Executable Vandermonde specification

**Claim.** For each executable Vandermonde input, the constructed matrix has nonzero column sums for every nonempty set of at most $k$ columns; its associated density is Fourier regular at level $k$ with bound zero; its row-span subspace has the stated cardinality bound; and the construction work has the displayed sum formula and polynomial-budget bound.

**Proof.** The proof assembles five established properties of the construction. The matrix has nonzero column sums for every nonempty set of at most $k$ columns (\texttt{FABL.executableVandermondeMatrix_hasNonzeroColumnSumsUpTo}); the associated density is Fourier regular at level $k$ with bound zero (\texttt{FABL.executableVandermondeDensity_isKWiseIndependent}); and the row-span subspace satisfies the stated cardinality bound (\texttt{FABL.executableVandermondeSubspace_card_le}). For the work identity, use the construction work formula as a traversal cost (\texttt{FABL.executableVandermondeConstructionWork_eq_sum}) and substitute the input's field degree, which is defined to be $\max(1,\mathrm{clog}(2,n))$. Finally, the construction work is at most the polynomial budget (\texttt{FABL.executableVandermondeConstructionWork_le_polynomialBudget}). Together these give the conjunction asserted.

**Key facts.** `FABL.executableVandermondeMatrix_hasNonzeroColumnSumsUpTo`, `FABL.executableVandermondeDensity_isKWiseIndependent`, `FABL.executableVandermondeSubspace_card_le`, `FABL.executableVandermondeConstructionWork_eq_sum`, `FABL.executableVandermondeConstructionWork_le_polynomialBudget`.
