<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/PTM.lean :: Randomized.RTIME.mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of Randomized Time

**Claim.** If $T_1(n)\le T_2(n)$ for every $n$, then every language in $\mathrm{RTIME}(T_1)$ belongs to $\mathrm{RTIME}(T_2)$.

**Proof.** Let $L\in\mathrm{RTIME}(T_1)$, witnessed by a constant $c$ and a finite randomized machine $N$ whose time bound is $n\mapsto cT_1(n)$. Since $T_1(n)\le T_2(n)$, multiplication by $c$ gives $cT_1(n)\le cT_2(n)$ for every input length. The machine therefore also randomized-decides $L$ within the latter bound, by monotonicity of randomized time deciders (`RDecidesInTime.mono`). Keeping the same constant and machine proves $L\in\mathrm{RTIME}(T_2)$.

**Key facts.** `Turing.FinNDTM.RDecidesInTime.mono`.
