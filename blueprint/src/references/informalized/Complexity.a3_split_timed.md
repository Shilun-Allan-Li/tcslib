<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/EXP.lean :: Complexity.a3_split_timed -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial time for split-word computation

**Claim.** For every pair of natural numbers $C,c$, there are a finite Turing machine over the binary alphabet and a natural number $A$ such that, on every binary input of length $n$, the machine computes the split word in exactly $A(n+1)^{c+2}$ steps.

**Proof.** First compute the binary representation of the padding quantity $C\cdot 2^{(r+1)^c}$ from an input of length $r$. The exponential-bits computation result (`a3_exp_bits_timed`) supplies a machine for this, running within a bound $B(r+1)^{c+1}$ for some constant $B$. Feed that machine into the split-solving construction (`computesFunInTime_splitSolveWith`), using the padding function $f(r)=C\cdot 2^{(r+1)^c}$. Its monotonicity hypothesis holds because increasing $r$ weakly increases $(r+1)^{c+1}$, and hence the bound $B(r+1)^{c+1}$. The construction gives a machine that solves the split and encodes the two pieces, with running time bounded by $D(n+1)(B(n+1)^{c+1}+n+2)$ for some constant $D$.

The search used by that construction agrees with the exponential-split search: both test the same equation, so their returned split points coincide. It remains to bound the displayed running time by a constant times $(n+1)^{c+2}$. Since $n+1\le(n+1)^{c+1}$ and $n+2\le 2(n+1)$, while $n+2\le 2^{c+1}(n+1)$, the terms inside the parentheses are bounded by $(B\cdot 2^{c+1}+2)(n+1)^{c+1}$. Multiplying by $D(n+1)$ yields the claimed form with $A=D(B\cdot 2^{c+1}+2)$. If necessary, the machine can run for any larger time bound while preserving its output, so the computation is realized in exactly that many steps.

**Key facts.** `Complexity.a3_exp_bits_timed`, `Turing.FinTM.computesFunInTime_splitSolveWith`, `Turing.FinTM.ComputesInTime.mono`.
