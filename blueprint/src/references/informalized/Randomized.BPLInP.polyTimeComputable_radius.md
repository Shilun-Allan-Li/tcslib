<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/BPLInPWords.lean :: Randomized.BPLInP.polyTimeComputable_radius -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Radius Computation

**Claim.** For every natural number $c$, the function sending a bit string $x$ to the binary representation of $c$ times one plus the length of the binary representation of $|x|$ is polynomial-time computable.

**Proof.** The input length's binary representation can be computed in linear time (\texttt{computesFunInTime\_lengthBits}), hence in polynomial time (\texttt{polyTimeComputable\_of\_linear}). Applying the unary-length construction produces a string of true bits whose length is one more than the length of that binary representation: compose with the unary constructor and append one constant true bit (\texttt{polyTimeComputable\_unary}, \texttt{PolyTimeComputable.comp}, \texttt{PolyTimeComputable.append}, and \texttt{polyTimeComputable\_const}). Next, by induction on $c$, construct $c$ copies of this unary string and concatenate them. The base case is the constant empty string; the successor case appends one further copy, using closure under concatenation (\texttt{PolyTimeComputable.append}). This gives a unary encoding of $c$ times the desired quantity. Finally, compose with the machine that converts the input string's length to its binary representation; the resulting binary value is exactly the radius (\texttt{PolyTimeComputable.comp}).

**Key facts.** `Turing.FinTM.computesFunInTime_lengthBits`, `Complexity.polyTimeComputable_of_linear`, `Complexity.polyTimeComputable_unary`, `Complexity.PolyTimeComputable.comp`, `Complexity.PolyTimeComputable.append`, `Complexity.polyTimeComputable_const`.
