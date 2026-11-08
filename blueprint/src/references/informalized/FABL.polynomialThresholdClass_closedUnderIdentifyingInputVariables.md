<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/PolynomialThresholdUniformStability.lean :: FABL.polynomialThresholdClass_closedUnderIdentifyingInputVariables -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Closure under identifying input variables

**Claim.** For every natural number $k$, the class of Boolean functions admitting a polynomial threshold representation of Fourier degree at most $k$ is closed under identifying input variables: substituting a map of coordinates into a function in the class produces another function in the class.

**Proof.** Take a function in the class on $n$ coordinates and a map from those coordinates to $m$ coordinates. Identifying inputs by this map is exactly the partition operation with every auxiliary sign fixed to $1$: at each input, both constructions evaluate the original function on the same tuple of selected coordinates. The partition-function closure theorem says that applying this operation preserves a polynomial threshold representation of Fourier degree at most $k$ (`isPolynomialThreshold_partitionFunction`). Applying it with the all-$1$ assignment proves the desired closure.

**Key facts.** `FABL.isPolynomialThreshold_partitionFunction`.
