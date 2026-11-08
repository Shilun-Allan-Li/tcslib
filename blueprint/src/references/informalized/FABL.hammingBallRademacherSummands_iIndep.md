<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/HammingBallLimit.lean :: FABL.hammingBallRademacherSummands_iIndep -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Independence of normalized signs

**Claim.** For every $n\ge 0$, under the uniform distribution on the sign cube, the coordinate signs normalized by $1/\sqrt n$ are mutually independent.

**Proof.** The uniform measure on the sign cube is the finite product of the uniform measures on each coordinate ($\texttt{hammingBallRademacherMeasure\_eq\_pi}$). Under this product measure, the coordinate projection maps are mutually independent. Applying the same function to each coordinate preserves this independence: here the function sends a sign $s$ to $s/\sqrt n$. Each such function is measurable because its domain is finite, so the product-measure independence theorem applies and gives the result.

**Key facts.** `FABL.hammingBallRademacherMeasure_eq_pi`.
