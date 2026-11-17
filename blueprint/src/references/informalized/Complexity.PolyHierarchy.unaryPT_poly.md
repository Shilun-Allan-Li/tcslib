<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/PolyHierarchy/Padding.lean :: Complexity.PolyHierarchy.unaryPT_poly -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomially bounded unary output

**Claim.** If $f$ is polynomial-time computable and $C,c\in\mathbb N$, then the function sending $y$ to a word of $C(|f(y)|+1)^c$ true bits is polynomial-time computable.

**Proof.** First consider the function on a string $x$ that outputs $C(|x|+1)^c$ true bits. The unary-output construction theorem gives a machine computing this function in time bounded by a polynomial: for the specified exponent $c$, its running-time exponent is $c+1$. Thus this unary-output function is polynomial-time computable. Compose it with the given polynomial-time computation of $f$. The composition theorem (`Complexity.PolyTimeComputable.comp`) shows the resulting function is polynomial-time computable; its value on $y$ is precisely a word of $C(|f(y)|+1)^c$ true bits.

**Key facts.** `Turing.FinTM.computesFunInTime_polyUnary`, `Complexity.PolyTimeComputable.comp`.
