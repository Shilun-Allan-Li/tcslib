<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/LowDegreeObstruction.lean :: lowDegreeSquarefreePolynomial_sum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Finite-sum additivity in the coefficient function

**Claim.** For a finite index set `S : Finset ι` and coefficients
`c : ι → LowDegreeSupport n D → K`,

`lowDegreeSquarefreePolynomial (fun s => ∑ i ∈ S, c i s) = ∑ i ∈ S, lowDegreeSquarefreePolynomial (c i)`.

**Proof.** `induction S using Finset.induction`.

* `empty`: both sides are the zero polynomial — `simp [lowDegreeSquarefreePolynomial_zero]`.
* `insert a S ha`: a three-step `calc`.
  1. Split the coefficient function: `congrArg lowDegreeSquarefreePolynomial` applied to a
     `funext s` proof that `∑ i ∈ insert a S, c i s = c a s + ∑ i ∈ S, c i s`, which is
     `simp [ha]` (`Finset.sum_insert`, using `ha : a ∉ S`).
  2. `rw [lowDegreeSquarefreePolynomial_add]` splits the constructor across the sum of two
     coefficient functions.
  3. `rw [ih]` on the tail term, then `simp [ha]` reassembles `Finset.sum_insert` on the
     right-hand side.

**Used in.** `lowDegree_squarefree_complete_on_rootCube`, to add up the per-monomial
squarefree representatives of a low-degree polynomial.
