<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.e3_exp_bits_timed -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-time computation of an exponential width

**Claim.** For fixed natural numbers $C,c$, there are a finite deterministic Turing machine $M$ and a natural number $A$ such that on every binary input $x$, $M$ outputs the binary expansion of $C\cdot2^{(|x|+1)^c}$ within $A(|x|+1)^{c+1}$ steps.

**Proof.** Split into the cases $C=0$ and $C\ne0$. If $C=0$, the desired output is always the empty string, so a machine computing a constant output suffices. Its linear time bound is at most a suitable constant times $(|x|+1)^{c+1}$. If $C\ne0$, first compute a unary string of length $(|x|+1)^c$ using the polynomial-time unary-power construction (\texttt{Turing.FinTM.computesFunInTime_polyUnary}). Then use the timed shift machine for the fixed word $\mathrm{bits}(C)$ to prepend that many zeros. The composition theorem for timed computations supplies a machine whose time is bounded by a constant times the sum of the two stage bounds, plus a fixed overhead (\texttt{Turing.FinTM.computesFunInTime_comp}). The binary-shift identity (\texttt{Complexity.e3_bits_shift}) identifies this output with the desired binary expansion.

To put the composition bound in the stated form, set $p=(|x|+1)^{c+1}$ and $k=|\mathrm{bits}(C)|+2$. Then $1\le p$ and $(|x|+1)^c\le p$. Consequently, the composition's terms, which are bounded by a constant multiple of $(|x|+1)^c p+k((|x|+1)^c p+1)+1$, are at most a suitable constant multiple of $(|x|+1)^{c+1}$. Increasing the overall constant gives the required $A$.

**Key facts.** `Turing.FinTM.computesFunInTime_const`, `Turing.FinTM.ComputesInTime.mono`, `Turing.FinTM.computesFunInTime_polyUnary`, `Turing.FinTM.computesFunInTime_comp`, `Complexity.e3_shift_timed`, `Complexity.e3_bits_shift`.
