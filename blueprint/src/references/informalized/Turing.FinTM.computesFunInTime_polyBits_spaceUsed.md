<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.computesFunInTime_polyBits_spaceUsed -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial binary output with bounded space

**Claim.** For every $C,e\in\mathbb{N}$, a finite Boolean-alphabet Turing machine outputs the least-significant-bit-first binary representation of $C(|x|+1)^e$ in polynomial time and uses at most a constant times $C(|x|+1)^e+1$ space at every time.

**Proof.** Separate the degenerate parameter cases first. If $C=0$, the desired output is the fixed representation of zero, so use the constant-output machine; its time and space bounds give the result. If $C>0$ and $e=0$, the output is the fixed representation of $C$, and the same constant-output result applies. In each case, the supplied time bound is enlarged to the required polynomial bound by monotonicity of powers, and the constant space bound is absorbed into the claimed expression.

For $C>0$ and $e=d+1$, form a buffered composition: the catalog machine first produces a unary string of length $C(|x|+1)^{d+1}$, then the counter machine converts the length of that string to binary. Their computation bounds, together with the buffered-composition time formula, give a bound no larger than $K(|x|+1)^{d+1}$ for $K=C+5(d+1)+4+6C+7$. Enlarging the constant to the theorem's chosen value preserves this time bound.

Finally, the general time-to-space estimate bounds the space through every time by the number of work tapes times the halting-time bound plus one. Since $C>0$, $(|x|+1)^{d+1}\le C(|x|+1)^{d+1}$; this comparison lets the resulting estimate be absorbed into $c\bigl(C(|x|+1)^{d+1}+1\bigr)$ for the chosen $c$.

**Key facts.** `Turing.FinTM.computesFunInTime_const_spaceUsed`, `Turing.FinTM.ComputesInTime.mono`, `Turing.FinTM.bufferedCompTM_computesInTime`, `Turing.FinTM.f2_catalogPoly_unary_computes`, `Turing.FinTM.f2_counter_computes`, `Turing.FinTM.f2_space_of_time`.
