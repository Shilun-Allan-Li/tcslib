<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/KarpLipton.lean :: Complexity.KarpLipton.innerLang_mem_coNP -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# CoNP membership of the inner language

**Claim.** If $V$ belongs to $\mathrm{P}$, then the language of strings $w$ for which every string $t$ gives $\langle w,t\rangle$ outside the bad language belongs to $\mathrm{coNP}$.

**Proof.** By definition, it suffices to show that the complement of the inner language belongs to $\mathrm{NP}$. Use the characterization of $\mathrm{NP}$ by polynomially bounded witnesses (\texttt{Complexity.mem_NP_iff_exists_length_le}), with verifier language $\mathrm{badLang}(C,c,V)$, which is in $\mathrm{P}$ by the closure result \texttt{Complexity.KarpLipton.badLang_mem_P}. For a string $w$ in the complement, there is some $t$ such that $z=\langle w,t\rangle$ is in the bad language. Choose as witness the encoding $\langle\langle \mathrm{gu}(z),\mathrm{gj}(z)\rangle,\mathrm{gp}(z)\rangle$. The bad-language membership characterization (\texttt{Complexity.KarpLipton.mem_badLang}) identifies these projections with the components used in the bad specification. The witness is polynomially bounded: the first decoded component has length at most $|w|$, by the bound on the length of a decoded first component (\texttt{Complexity.length_pairFstD_le}); the three components extracted from $z$ satisfy the length bounds in the bad specification. The formula for pair-encoding length (\texttt{Turing.length_pairEncode}) then bounds the witness length by $(7C+6)(|w|+1)^c$. Finally, encoding $w$ with this witness preserves all five decoded components: decoding the newly formed nested pair returns the same projections as decoding $z$. Thus the verifier accepts. Conversely, if a polynomially bounded witness makes the verifier accept on $w$, the same projection identities show that $\langle w,t\rangle$ belongs to the bad language for the witness's second component $t$. Hence $w$ is outside the inner language, proving the required equivalence.

**Key facts.** `Complexity.mem_NP_iff_exists_length_le`, `Complexity.KarpLipton.badLang_mem_P`, `Complexity.KarpLipton.mem_badLang`, `Complexity.length_pairFstD_le`, `Turing.length_pairEncode`.
