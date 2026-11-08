<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/NTIME.lean :: Complexity.NTIME.mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of Nondeterministic Time

**Claim.** If $T_1(n)\le T_2(n)$ for every $n$, then every language in $\mathrm{NTIME}(T_1)$ also belongs to $\mathrm{NTIME}(T_2)$.

**Proof.** Let $L$ be decided within $cT_1(n)$ steps by a nondeterministic machine $N$. For an input $x$, the pointwise bound gives $cT_1(|x|)\le cT_2(|x|)$. Thus every computation branch halts within the larger bound, by monotonicity of `HaltsWithin`. If $x\in L$, an accepting branch of the shorter prescribed length extends to the longer length by `AcceptsWithin.mono`, so acceptance is preserved. Conversely, suppose a choice word $w$ of length $cT_2(|x|)$ halts and accepts. Keep just its first $cT_1(|x|)$ choices. This prefix has the shorter length; the original run splits into the run on the prefix followed by the run on the remaining suffix, by `runWith_append`. Since the prefix run has already halted, `runWith_of_halt` says the suffix does not change its configuration. The prefix therefore halts with the same accepting output, so $x$ was accepted within the shorter bound. The same machine and constant $c$ consequently decide $L$ within $cT_2$.

**Key facts.** `Turing.NDTM.HaltsWithin.mono`, `Turing.FinNDTM.AcceptsWithin.mono`, `Turing.NDTM.runWith_append`, `Turing.NDTM.runWith_of_halt`.
