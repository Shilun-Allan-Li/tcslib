<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Constructible.lean :: Complexity.spaceConstructible_linear -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Linear space constructibility

**Claim.** The function $S(n)=n+1$ is space constructible: its logarithmic lower bound holds, and a finite binary Turing machine outputs the binary digits of $|x|+1$ using at most a constant multiple of $|x|+1$ work-tape cells.

**Proof.** First, the standard inequality $\lfloor\log_2 n\rfloor\le n$ gives $\lfloor\log_2 n\rfloor+1\le n+1$. For the machine, take one that prepends the bit $1$ to its input and one that computes the binary digits of the input length. Compose them using the buffered composition construction. The prepend machine uses a fixed number $a$ of cells, and the length-bits machine uses at most $b(m+1)$ cells on an input of length $m$, for constants $a,b$. Applied to the prepended word $[1]\mathbin{++}[x]$, the composition outputs the binary digits of $|x|+1$; its running time is $a(|x|+1)+(|x|+1)+2+b(|x|+2)$. This time plus one is bounded by $(a+2b+4)(|x|+1)$. A machine with $k$ work tapes uses at most $k(t+1)$ cells in $t$ steps (`Turing.MultiTapeTM.spaceUsed_le_mul_succ`), so the composite uses at most $k(a+2b+4)(|x|+1)$ cells. Choosing the positive constant $c=k(a+2b+4)+1$ gives the required bound.

**Key facts.** `Turing.FinTM.computesFunInTime_prepend_spaceUsed`, `Turing.FinTM.computesFunInTime_lengthBits_spaceUsed`, `Turing.FinTM.bufferedCompTM_computesInTime`, `Turing.MultiTapeTM.spaceUsed_le_mul_succ`.
