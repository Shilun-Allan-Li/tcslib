<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/MajorityFourierTailAsymptotics.lean :: FABL.integral_Ioi_two_mul_add_one_rpow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Half-Line Integral of a Power

**Claim.** If $s<-1$ and $a\ge0$, then $\int_{x>a}(2x+1)^s\,dx=-(2a+1)^{s+1}/(2(s+1))$.

**Proof.** Set $F(x)=(2x+1)^{s+1}/(2(s+1))$. Since $a\ge0$, the base $2x+1$ is positive for $x\ge a$, and differentiation gives $F'(x)=(2x+1)^s$. The integrand is integrable on $(a,\infty)$ (`integrableOn_two_mul_add_one_rpow`). As $x\to\infty$, the base tends to infinity and $s+1<0$, so $F(x)\to0$. The improper fundamental theorem of calculus now gives the integral as $F(\infty)-F(a)$, which is the stated expression.

**Key facts.** `FABL.integrableOn_two_mul_add_one_rpow`.
