<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean :: Turing.not_mem_roundStop -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# States outside the stop set

**Claim.** An option state lies outside the set formed from the absent state, the present state $a$, and all elements of $E$ exactly when it is a present state $s$ with $s\ne a$ and $\mathrm{some}(s)\notin E$.

**Proof.** Suppose first that $q$ is outside the stop set. It cannot be absent, since the absent state is included, so write $q=\mathrm{some}(s)$. It cannot equal $\mathrm{some}(a)$, hence $s\ne a$. Nor can $\mathrm{some}(s)$ belong to $E$, since $E$ is included in the stop set. Conversely, suppose $q=\mathrm{some}(s)$ with $s\ne a$ and $\mathrm{some}(s)\notin E$. If $q$ belonged to the stop set, it would be absent, equal to $\mathrm{some}(a)$, or an element of $E$. The first is impossible for a present state, the second contradicts $s\ne a$, and the third contradicts the assumption on $E$. Thus $q$ is outside the set.
