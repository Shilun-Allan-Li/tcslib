<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/ThresholdFunctionCounting.lean :: FABL.fourierCoeff_eq_agreementCount -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier Coefficient from Agreement Count

**Claim.** For a sign-valued function on the $n$-dimensional cube, its Fourier coefficient at $S$ is $(2A-2^n)/2^n$, where $A$ counts inputs on which the function agrees with the parity on $S$.

**Proof.** The Fourier coefficient is the average of the product of the real-valued function and the monomial on $S$. The parity function on $S$ has real-valued version equal to that monomial (`parityFunction_toReal`). Since both factors take values in $\{-1,1\}$, their product is $1$ exactly at inputs where the function agrees with that parity, and is $-1$ at every other input. Thus the sum of these products over the cube is $A-(2^n-A)=2A-2^n$. The cube has $2^n$ inputs, so dividing this sum by its cardinality gives the stated coefficient.

**Key facts.** `FABL.parityFunction_toReal`.
