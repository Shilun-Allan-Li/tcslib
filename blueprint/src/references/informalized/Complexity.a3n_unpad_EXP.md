<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.a3n_unpad_EXP -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unpadding into Exponential Time

**Claim.** If the language of encodings of pairs $(x,p)$, where $x\in L$ and $p$ is the prescribed all-ones padding, belongs to $\mathrm{P}$, then $L\in\mathrm{EXP}$.

**Proof.** By the characterization of polynomial time, choose a decider $D$ for the padded language with a polynomial running-time bound (`Complexity.mem_P_iff`). The padding can be written in time bounded by a polynomial in $m=n+C2^{(3(n+1))^c}+1$ (`Complexity.a3n_pad_emit`); for input $x$, let $y$ be the encoding of $x$ together with its required all-ones padding. Its length is $2|x|+2+C2^{(|x|+1)^c}$, and the padding length is no larger than the corresponding term with exponent input $3(|x|+1)$. In particular, $|y|+1\le 3m$.

The padded-language membership test on $y$ agrees with the test for $x\in L$, because this encoding has exactly the required padding (`Complexity.a3n_pad_member`). Run the padding machine and then $D$ on its output. The composition bound for these computations (`Complexity.a3n_comp_at`) gives time at most the padding time, the output length and fixed overhead, and $D$'s polynomial time on $y$. Since $|y|+1\le3m$, and $m$ dominates the relevant powers, this total is at most $K m^r$ for the proof's choices $r=c+2+d+1$ and $K=B+4+A3^d$. Finally, the scaled exponential envelope (`Complexity.a3n_scaled_envelope`) bounds this by $a(2^{|x|})^e$ for suitable constants $a,e$. Thus the resulting decider for $L$ has an exponential time bound, placing $L$ in $\mathrm{EXP}$.

**Key facts.** `Complexity.mem_P_iff`, `Complexity.a3n_pad_emit`, `Complexity.a3n_pad_member`, `Complexity.a3n_comp_at`, `Complexity.a3n_scaled_envelope`, `Turing.FinTM.ComputesInTime.mono`.
