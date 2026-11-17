<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomWalkMixing.lean :: Randomized.RegularMultigraph.uniformExcess_walkDist_mul_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Iterated Uniform-Excess Contraction

**Claim.** If every probability function contracts uniform excess by a factor at most $c$ after $K$ steps, then after $iK$ steps its uniform excess is at most $c^i$ times its initial uniform excess.

**Proof.** Proceed by induction on $i$. For $i=0$, the zero-step walk leaves the distribution unchanged (`walkDist_zero`), giving the claim since $c^0=1$. For the induction step, write $(i+1)K=iK+K$. The composition law for walks (`walkDist_add`) identifies the distribution after these steps with the result of applying the $K$-step walk to the distribution after $iK$ steps. That intermediate distribution still has total mass $1`, because `sum_walkDist` preserves the sum of the values. The assumed $K$-step contraction applies, and the induction hypothesis bounds its right-hand side. Since $c
earrow0$, multiplying the induction inequality by $c$ preserves its direction; the resulting factor $c(c^i)$ equals $c^{i+1}$ by the power rule.

**Key facts.** `Randomized.RegularMultigraph.walkDist_zero`, `Randomized.RegularMultigraph.walkDist_add`, `Randomized.RegularMultigraph.sum_walkDist`.
