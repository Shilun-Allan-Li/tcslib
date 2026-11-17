<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFHardVerifier.lean :: Complexity.TQBFHard.pt_vlen -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Unary Configuration Length

**Claim.** For each input string $y$, the unary string of length $V_{N,d,c}(|x|)$, where $x$ is its decoded first component, is polynomial-time computable.

**Proof.** Write $x$ for the decoded first component of $y$. The length in question is the sum of three terms: $4dW_N(|x|+1)^c$, $W_N+1$, and the number of binary digits of $|x|+1$. For the first term, the polynomial unary-length construction gives a polynomial-time output as a function of $|x|$; composing with the first-component decoder preserves polynomial time (`polyTimeComputable_polyUnary`, `PolyTimeComputable.comp`, `polyTimeComputable_pairFstD`). The second term is a fixed unary string, hence polynomial-time computable (`polyTimeComputable_const`). For the third term, append a single true bit to $x$, compute the bit-list representation of the resulting length, and then output a unary string whose length is that bit-list's length. Appending the fixed bit and computing the binary digits of a string's length are polynomial-time operations; the unary-length construction and composition therefore give the required third output (`PolyTimeComputable.append`, `polyTimeComputable_const`, `Turing.FinTM.computesFunInTime_lengthBits`, `polyTimeComputable_of_linear`, `polyTimeComputable_unary`, `PolyTimeComputable.comp`, `polyTimeComputable_pairFstD`). Concatenate the three unary strings using polynomial-time closure under append (`PolyTimeComputable.append`). Their lengths sum to the stated configuration-length expression: the binary-digit term is the digit length of $|x|+1$, and the remaining arithmetic agrees by the definitions of $V_{N,d,c}$, $W_N$, and the radius. Hence the concatenated output is precisely the desired unary string.

**Key facts.** `Complexity.polyTimeComputable_polyUnary`, `Complexity.polyTimeComputable_pairFstD`, `Complexity.PolyTimeComputable.comp`, `Complexity.polyTimeComputable_const`, `Complexity.PolyTimeComputable.append`, `Turing.FinTM.computesFunInTime_lengthBits`, `Complexity.polyTimeComputable_of_linear`, `Complexity.polyTimeComputable_unary`.
