<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/EXP.lean :: Complexity.a3_exp_bits_timed -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Timed Binary Exponential Output

**Claim.** For any natural numbers $C,c$, a finite binary Turing machine outputs the binary digits of $C\,2^{(|x|+1)^c}$ on every Boolean input $x$, within a bound $A(|x|+1)^{c+1}$ for some natural number $A$.

**Proof.** First suppose $C=0$. A constant-output machine produces the empty word, which is the binary expansion of zero. Its linear time bound is dominated by a suitable multiple of $(|x|+1)^{c+1}$, since this power is at least one. Now suppose $C\ne0$. A unary-output machine produces a word of $m=(|x|+1)^c$ true symbols in time at most $a(|x|+1)^{c+1}$, by the polynomial unary-output theorem (`computesFunInTime_polyUnary`). Feed this word to a machine that shifts the binary expansion of $C$ by prepending as many zeroes as the input length. The composition theorem gives a machine computing the composition, with time bounded by a constant $b$ times the unary machine’s time plus the shift machine’s time on that output (`computesFunInTime_comp`). The shift machine’s running-time function is monotone as required by that theorem. The binary-shift identity says that the result is $m$ zeroes followed by the bits of $C$, precisely the binary expansion of $C2^m$ (`a3_bits_shift`); the shift machine’s time bound is $(\operatorname{length}(\operatorname{bits}(C))+2)(m+1)$ (`a3_shift_timed`). Put $p=(|x|+1)^{c+1}$. Since $p\ge1$ and $m\le p$, the resulting bound is at most $b(a+1)(\operatorname{length}(\operatorname{bits}(C))+3)p$. Choosing this coefficient as $A$ establishes the claimed bound.

**Key facts.** `Turing.FinTM.computesFunInTime_const`, `Turing.FinTM.ComputesInTime.mono`, `Turing.FinTM.computesFunInTime_polyUnary`, `Turing.FinTM.computesFunInTime_comp`, `Complexity.a3_bits_shift`, `Complexity.a3_shift_timed`.
