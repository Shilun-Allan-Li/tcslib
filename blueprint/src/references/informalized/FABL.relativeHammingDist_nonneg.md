<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/FKN.lean :: FABL.relativeHammingDist_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonnegativity of Relative Hamming Distance

**Claim.** For a finite nonempty set $\Omega$, a set $\beta$ with decidable equality, and functions $f,g:\Omega\to\beta$, their relative Hamming distance is nonnegative.

**Proof.** Relative Hamming distance is the Hamming distance divided by the cardinality of the domain. The numerator is nonnegative, and the denominator is positive because the domain is finite and nonempty. The quotient is therefore nonnegative.
