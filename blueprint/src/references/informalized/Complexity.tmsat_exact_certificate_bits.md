<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/TMSAT.lean :: Complexity.tmsat_exact_certificate_bits -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-time certificate bits

**Claim.** For all natural numbers $C,c$, the function sending a bit string $x$ to the bit-list representation of $C(|x|+1)^c$ is polynomial-time computable.

**Proof.** If $C=0$, the output is always the empty bit string, so the constant-output computation suffices. If $C>0$ but $c=0$, the output is the fixed bit representation of $C$, again computed in constant time. In the remaining case, $C>0$ and $c>0$. Apply the polynomial time-constructibility result for $C(n+1)^{(c-1)+1}$ (timeConstructible_poly) to obtain a machine producing the required bit representation in time bounded by a constant multiple of this function. Since $(c-1)+1=c$, its output on input $x$ is the desired representation. To put its time bound in the required polynomial form, use $(|x|+1)^c\geq1$ to bound $C(|x|+1)^c+1$ by $(C+1)(|x|+1)^c$. Increasing the machine's time constant accordingly gives a polynomial-time computation of the output.

**Key facts.** `Complexity.tmsat_constant_poly`, `Complexity.timeConstructible_poly`, `Turing.FinTM.ComputesInTime.mono`.
