<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/OrthogonalDecomposition.lean :: FABL.firstCoordinates_dimension -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial coordinates in full dimension

**Claim.** Among $n$ coordinates, the first $n$ coordinates comprise the full coordinate set.

**Proof.** A coordinate index $i$ belongs to the first-$n$ set exactly when its value is less than $n$. Every element of $\mathrm{Fin}(n)$ has value less than $n$, so this condition holds for every coordinate; hence the filtered set is the whole coordinate set.
