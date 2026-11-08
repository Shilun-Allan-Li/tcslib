<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/TMSAT.lean :: Complexity.tmsat_certificate_unary -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unary certificate length computation

**Claim.** For all natural numbers $C,c$, the function sending a bit string $x$ to the word of $C(|x|+1)^c$ ones is polynomial-time computable.

**Proof.** If $C=0$, the output is always empty, so the constant-function result (`Complexity.polyTimeComputable_const`) applies. If $C\ne0$ but $c=0$, the output is always the fixed word of $C$ ones, and the same result applies. In the remaining case, apply the unary-output machine theorem (`Turing.FinTM.computesFunInTime_polyUnary`) with exponent $c-1+1$. Since $c\ne0$, this exponent equals $c$, so the machine outputs the desired number of ones. Its time bound has exponent $(c-1+1)+1=c+1$, which is a polynomial bound of the required form.

**Key facts.** `Complexity.polyTimeComputable_const`, `Turing.FinTM.computesFunInTime_polyUnary`.
