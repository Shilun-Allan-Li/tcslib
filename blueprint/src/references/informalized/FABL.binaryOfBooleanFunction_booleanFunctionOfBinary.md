<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/DNFFormulas.lean :: FABL.binaryOfBooleanFunction_booleanFunctionOfBinary -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Inverse Binary Function Conversion

**Claim.** For every $n$ and every function $f$ from the binary cube $\mathbb F_2^n$ to the sign set $\{-1,1\}$, converting $f$ to a function on the sign cube and then back to the binary cube recovers $f$ exactly.

**Proof.** Evaluate the two functions at an arbitrary binary vector $x$. By definition, the conversion to the sign cube evaluates $f$ at the inverse image of its input under the binary-to-sign cube equivalence; converting back supplies that equivalence applied to $x$. These maps are inverses, so the resulting input to $f$ is exactly $x$. Since the values agree at every $x$, the functions are equal.
