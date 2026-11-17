<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Randomization/Basic.lean :: BooleanAnalysis.Hypercontractivity.RandomizationAux.sum_powerset_signed_sum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Signed Subset Inversion

**Claim.** For a finite set $U$, the double alternating sum over $S\subseteq U$ and $T\subseteq S$ equals $g(U)$.

**Proof.** Induct on $U$. If $U$ is empty, the only pair is $S=T=\varnothing$, and the sum is $g(\varnothing)$. For the induction step, write $U=V\cup\{i\}$ with $i\notin V$ and split the outer subsets according to whether they contain $i$. Regrouping the resulting terms, and then splitting each inner subset according to whether it contains $i$, cancels the contributions so that the double sum for $U$ becomes the same double sum on $V$ applied to the function $T\mapsto g(T\cup\{i\})$. The induction hypothesis evaluates this as $g(V\cup\{i\})=g(U)$. The signs in this regrouping oppose in the paired terms because adjoining $i$ increases both relevant cardinalities by one.
