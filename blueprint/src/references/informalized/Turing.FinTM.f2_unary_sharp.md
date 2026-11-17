<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_unary_sharp -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unary Output in Polynomial Time

**Claim.** For every $C,e\in\mathbb N$, there are a finite Boolean-alphabet machine and a constant $a$ that compute $C(n+1)^e$ copies of true on every input of length $n$ within $a((n+1)^e+n+1)$ steps.

**Proof.** Split on the exponent. If $e=0$, use the constant-output machine for the word of $C$ true symbols (`computesFunInTime_const_spaceUsed`). It computes that word within $a(n+1)$ steps. Since $n+1\le (n+1)+n+1$, this time is at most the claimed bound, and the output length is $C=C(n+1)^0$. Monotonicity of computation time (`ComputesInTime.mono`) allows the runtime bound to be increased.

If $e=d+1$, use the polynomial unary-output machine (`f2_catalogPoly_unary_computes`) with degree parameter $d$ and coefficient $C$. It outputs the required $C(n+1)^{d+1}$ symbols within $(C+5(d+1)+4)(n+1)^{d+1}$ steps. Since $(n+1)^{d+1}\le (n+1)^{d+1}+n+1$, this is bounded by the claimed expression for $a=C+5(d+1)+4$; again, runtime monotonicity permits the stated bound.

**Key facts.** `Turing.FinTM.computesFunInTime_const_spaceUsed`, `Turing.FinTM.ComputesInTime.mono`, `Turing.FinTM.f2_catalogPoly_unary_computes`.
