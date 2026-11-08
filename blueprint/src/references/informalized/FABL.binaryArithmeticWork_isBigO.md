<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/ExecutableFiniteFields.lean :: FABL.binaryArithmeticWork_isBigO -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Quadratic Arithmetic Work Bound

**Claim.** As $\ell$ tends to infinity, the binary arithmetic work is $O((\ell+1)^2)$.

**Proof.** The explicit bound states that for every $\ell$, the arithmetic work is at most $8(\ell+1)^2$ (`binaryArithmeticWork_le`). Regarding both sides as real-valued functions, this uniform bound gives the required Big-O estimate with constant $8$.

**Key facts.** `FABL.binaryArithmeticWork_le`.
