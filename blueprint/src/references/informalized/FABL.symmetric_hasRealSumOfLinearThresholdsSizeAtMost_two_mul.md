<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/ThresholdCircuits.lean :: FABL.symmetric_hasRealSumOfLinearThresholdsSizeAtMost_two_mul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Symmetric functions as threshold sums

**Claim.** Every symmetric sign-valued Boolean function on the $n$-dimensional sign cube is a real constant plus a sum of at most $2n$ linear threshold functions.

**Proof.** Define the count profile $a(k)$ by evaluating $f$ on a canonical input with $k$ positive coordinates. Symmetry implies that two inputs with the same number of positive coordinates have the same function value ($\texttt{isSymmetric_iff_eq_of_positiveCoordinateCount_eq}$). For any input $x$, the canonical input indexed by its positive-coordinate count has the same count: the count of the canonical input at parameter $k$ is $\min(n,k)$ ($\texttt{positiveCoordinateCount_canonicalCountInput}$), and the count of $x$ is at most $n$ ($\texttt{positiveCoordinateCount_le}$). Thus $f(x)=a(\mathrm{count}(x))$. The count-profile representation theorem then expresses $f$ as a real constant plus a sum of $2n$ linear threshold functions ($\texttt{isRealSumOfLinearThresholds_of_count_profile}$). Since $2n\le2n$, this is the required size bound.

**Key facts.** `FABL.isSymmetric_iff_eq_of_positiveCoordinateCount_eq`, `FABL.positiveCoordinateCount_canonicalCountInput`, `FABL.positiveCoordinateCount_le`, `FABL.isRealSumOfLinearThresholds_of_count_profile`.
