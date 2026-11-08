<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/NSPACE.lean :: Complexity.NSPACE.mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of Nondeterministic Space

**Claim.** If $s_1(n)\le s_2(n)$ for every $n$, then $\mathrm{NSPACE}(s_1)\subseteq\mathrm{NSPACE}(s_2)$.

**Proof.** Let $L\in\mathrm{NSPACE}(s_1)$, witnessed by a constant $c$ and a nondeterministic machine. For each input $x$, retain the same halting time and the same acceptance behavior. On every choice sequence $w$ of the required length, the space used is at most $c\,s_1(|x|)$. By the assumed pointwise inequality and monotonicity of multiplication by $c$, this is at most $c\,s_2(|x|)$. Thus the same machine witnesses $L\in\mathrm{NSPACE}(s_2)$.
