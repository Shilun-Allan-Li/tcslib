<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/ChoiceWords.lean :: Turing.choiceBudget_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial Choice Budget Bound

**Claim.** For all natural numbers $a,c,n$, one has $a(n^c+1)\le 2a(n+1)^c$.

**Proof.** Since $n\le n+1$, monotonicity of natural powers gives $n^c\le(n+1)^c$. Also $1\le(n+1)^c$, since $n+1$ is positive. Adding these inequalities yields $n^c+1\le 2(n+1)^c$. Multiplication by $a$ preserves the inequality, and rearranging the product on the right gives the claimed bound.
