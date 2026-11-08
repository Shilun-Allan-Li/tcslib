<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Diagonalization/Relativization.lean :: Complexity.unaryWitnessLang_mem_NPOracle -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unary Witnesses in Nondeterministic Polynomial Time

**Claim.** For every language $B$ of finite Boolean words, the language of all-true unary strings whose length-$n$ witness belongs to $B$ is in nondeterministic polynomial time with oracle $B$.

**Proof.** Use the machine and its branch analysis supplied by `uw_branch`. Choose exponent $1$ and the machine `uwTM`; its running-time bound at input length $n$ is a constant multiple of $n+1$. The first conclusion of `uw_branch` says every choice string of the prescribed length halts. For a word $x$ in the unary-witness language, write $x=1^n$ and choose a witness $y\in B$ of length $n$. Extend $y$ by $2n+3$ zero bits. This choice string has the required run length, and its first $n$ bits are $y$, while the next $2n+3$ bits provide the machine's required tail. Since every bit of $x$ is true, `uw_branch` ensures the machine accepts exactly when that prefix belongs to $B$, so this choice is accepting. Conversely, suppose a choice string of the prescribed length yields acceptance. By `uw_branch`, every bit of $x$ is true and the prefix of length $|x|$ belongs to $B$. Taking $n=|x|$ gives $x=1^n$, and that prefix is a length-$n$ witness in $B$. Thus acceptance is equivalent to membership, and the chosen machine decides the language within the stated polynomial bound.

**Key facts.** `Complexity.uw_branch`.
