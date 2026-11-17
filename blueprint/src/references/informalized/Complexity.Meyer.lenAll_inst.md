<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Meyer.lean :: Complexity.Meyer.lenAll_inst -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length consistency for encoded inputs

**Claim.** Under the stated bounds on $j$, the length-consistency atom evaluates to true on the encoded tuple with width-bounded words for $t$ and $a$, a run of $j$ ones, and enough zeros to fill the width.

**Proof.** Write $W=C_w(|x|+1)^{c_w}$. The decoded components of the encoded tuple are exactly $x$, the width-$W$ words for $t$ and $a$, the run of $j$ ones, and the specified zero string. The width words each have length $W$ (`length_enumWord`), and the run of ones has length $j$. The binary length of $j$ is at most $W$: the hypothesis $j<2^W$ gives this via the binary-size bound. Hence the appended zero string has length $W-\ell$, where $\ell$ is the binary length of $j$, so the combined length measured by the atom is $\ell+(W-\ell)=W$. The remaining required condition is $j\le |x|+1$, which is assumed. All three conjuncts defining the atom's length check therefore hold, so its Boolean value is true.

**Key facts.** `Complexity.Meyer.vt_vin`, `Complexity.Meyer.va_vin`, `Complexity.Meyer.vj_vin`, `Complexity.Meyer.vx_vin`, `Complexity.Meyer.length_enumWord`.
