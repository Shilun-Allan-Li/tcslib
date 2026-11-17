<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/FourierToF₂Polynomial.lean :: FABL.booleanNumericalCoeffInt_cast_f₂_eq_anfCoeff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Integer Coefficient Modulo Two

**Claim.** Reducing the integer numerical coefficient modulo two gives the algebraic-normal-form coefficient indexed by $S$.

**Proof.** Expand the integer coefficient as its sum over subsets $T\subseteq S$ and reduce the sum term by term modulo two. In each summand, the factor $(-1)^{|S|-|T|}$ becomes $1$ in the field with two elements. If $f$ evaluates to $1$ on the vector with ones exactly in $T$, the remaining indicator is $1$, giving the corresponding summand of the algebraic-normal-form coefficient. If it does not evaluate to $1$, its value is $0$, since every element of the two-element field is either $0$ or $1$; the indicator and the corresponding algebraic-normal-form summand are then both zero. Thus the summands agree for every $T$, and so do their sums.
