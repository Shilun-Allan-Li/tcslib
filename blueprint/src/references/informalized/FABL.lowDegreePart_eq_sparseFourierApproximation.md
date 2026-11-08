<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/DNFFourier.lean :: FABL.lowDegreePart_eq_sparseFourierApproximation -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Low-degree part as sparse Fourier approximation

**Claim.** For every degree cutoff and real-valued function on the sign cube, its low-degree part equals the sparse Fourier approximation formed from all subsets of size at most that cutoff, with the Fourier coefficients as coefficients.

**Proof.** Both sides are defined pointwise by the same finite sum: over precisely those subsets $S$ with $|S|\le k$, each summand is the Fourier coefficient of $f$ at $S$ multiplied by the monomial indexed by $S$. Hence the two functions are equal by unfolding their definitions.
