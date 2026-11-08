<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/ModThree.lean :: FABL.modThreeCubicProduct_re -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Real Part of the Cubic Product

**Claim.** The real part of the cubic product is $(-\frac12)^n$ times the sum over even-cardinality subsets $S$ of $(-1)^{(|S|\bmod 4)/2}(\sqrt3)^{|S|}m_S(x)$.

**Proof.** Start with the complex product expansion (\texttt{FABL.modThreeCubicProduct_expansion}) and take real parts. The real scalar factor $(-1/2)^n$ passes through the real-part operation, and the real part of a finite sum is the sum of the real parts of its terms. The termwise real-part formula (\texttt{FABL.modThreeComplexTerm_re}) says that an odd-cardinality subset contributes zero, while an even-cardinality subset contributes $(-1)^{(|S|\bmod 4)/2}(\sqrt3)^{|S|}m_S(x)$. Removing the zero terms leaves exactly the sum over even-cardinality subsets.

**Key facts.** `FABL.modThreeCubicProduct_expansion`, `FABL.modThreeComplexTerm_re`.
