<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.computesFunInTime_polyBits -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial values in binary

**Claim.** For every pair of natural numbers $C,e$, a finite Boolean-alphabet Turing machine outputs the least-significant-bit-first binary representation of $C(|x|+1)^e$ in at most a constant times $(|x|+1)^{e+1}$ steps.

**Proof.** First compute the unary string of length $C(|x|+1)^e$ using the unary polynomial-output machine, with time constant $a$. Then apply the machine that returns the binary representation of a string's length, with time constant $b$. The composition theorem gives a machine for the desired binary output and a bound of the form $d\bigl(a(|x|+1)^{e+1}+b(a(|x|+1)^{e+1}+1)+1\bigr)$.

Let $P=(|x|+1)^{e+1}$, so $P\ge1$. The expression inside the outer factor is at most $(a+1)(b+1)P$: expanding the left side gives $a(b+1)P+(b+1)$, and $b+1\le(b+1)P$. Thus the time is at most $d(a+1)(b+1)P$. Taking this product as the new constant proves the claim.

**Key facts.** `Turing.FinTM.computesFunInTime_polyUnary`, `Turing.FinTM.computesFunInTime_lengthBits`, `Turing.FinTM.computesFunInTime_comp`, `Turing.FinTM.ComputesInTime.mono`.
