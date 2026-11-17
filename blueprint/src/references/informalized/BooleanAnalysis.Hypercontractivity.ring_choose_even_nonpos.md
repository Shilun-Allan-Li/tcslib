<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Cube/Reverse/TwoPoint.lean :: BooleanAnalysis.Hypercontractivity.ring_choose_even_nonpos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Signs of even generalized binomial coefficients

**Claim.** For $0<s<1$ and every integer $k\ge1$, the generalized binomial coefficient $\binom{s}{2k}$ is nonpositive.

**Proof.** Use strong induction on $k$. At $k=1$, the explicit formula $\binom{s}{2}=s(s-1)/2$ is nonpositive because $s>0$ and $s-1<0$ (`ring_choose_two`). For the induction step, write the next even coefficient using the recurrence `ring_choose_even_succ`: it is the preceding even coefficient multiplied by $(s-2(k+1))(s-(2(k+1)+1))$ and divided by the positive number $(2(k+1)+1)(2(k+1)+2)$. Both factors in the numerator are nonpositive since $s<1$, so their product is nonnegative. The induction hypothesis therefore makes the whole quotient nonpositive, completing the induction.

**Key facts.** `BooleanAnalysis.Hypercontractivity.ring_choose_two`, `BooleanAnalysis.Hypercontractivity.ring_choose_even_succ`.
