<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Basic.lean :: Complexity.BinArith.polyTimeComputable_cons -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Prefixing a Computable Output

**Claim.** If the Boolean-valued function $p$ and the bit-string-valued function $f$ are polynomial-time computable, then so is the function $x\mapsto p(x)::f(x)$.

**Proof.** The one-bit output $[p(x)]$ and the output $f(x)$ are polynomial-time computable by hypothesis. The closure of polynomial-time computability under concatenation (\texttt{Complexity.PolyTimeComputable.append}) therefore gives that $x\mapsto [p(x)]++f(x)$ is polynomial-time computable. This concatenation is exactly the prefixed output $p(x)::f(x)$.

**Key facts.** `Complexity.PolyTimeComputable.append`.
