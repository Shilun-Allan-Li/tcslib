<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Randomization/Centered.lean :: BooleanAnalysis.Hypercontractivity.CenteredContraction.scalar_contraction_generic -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniform reflected contraction

**Claim.** For every real $q\ge 2$, there is a real $c$ with $0<c\le 1$ such that, for every real $x$, $|1-cx|^q\le |1+x|^q-q(1+c)x$.

**Proof.** Choose $M>0$ so that the remainder $R_q(y)=|1+y|^q-1-qy$ is bounded above by $M(y^2+|y|^q)$ for every $y$; this is the remainder upper bound (`remainder_upper`). The remainder is nonnegative and controls both terms in $x^2+|x|^q$: the lower bound gives $x^2\le R_q(x)$ (`remainder_lower`), while the power lower bound gives $|x|^q\le 2^q(q+3)R_q(x)$ (`remainder_power_lower`). Set $B=2^q(q+3)$, $A=M(1+B)$, and $c=1/(1+A)$. Then $0<c\le1$ and $Ac^2\le1$. Also, since $q\ge2$ and $c\le1$, $c^q\le c^2$. Apply the upper remainder estimate at $y=-cx$. Using $|cx|^q=c^q|x|^q$ and the preceding bounds yields $R_q(-cx)\le Mc^2(x^2+|x|^q)\le Ac^2R_q(x)\le R_q(x)$. Expanding the two remainders and rearranging gives the claimed inequality.

**Key facts.** `BooleanAnalysis.Hypercontractivity.CenteredContraction.remainder_upper`, `BooleanAnalysis.Hypercontractivity.CenteredContraction.remainder_lower`, `BooleanAnalysis.Hypercontractivity.CenteredContraction.remainder_power_lower`.
