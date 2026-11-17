<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Products/Basic.lean :: BooleanAnalysis.Hypercontractivity.sum_powerset_signed_inter -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Subset intersection cancellation

**Claim.** For every finite $U\subseteq\alpha$, summing $E_S(g)$ over all subsets $S\subseteq U$ recovers $g(U)$.

**Proof.** Proceed by induction on the finite set $U$, with the induction statement uniform in the function $g$. If $U=\varnothing$, the only subset is empty and its energy is $g(\varnothing)$, giving the result. For the induction step write $U'=U\cup\{i\}$ with $i\notin U$. Split the subsets of $U'$ into those contained in $U$ and those containing $i$. The former contribute $\sum_{S\subseteq U}E_S(g)$. For each $S\subseteq U$, the latter contribution at $S\cup\{i\}$ is $E_S(T\mapsto g(\{i\}\cup T))-E_S(g)$, by the insertion identity for signed intersection energy (\texttt{signedIntersectionEnergy\_insert}); here $i\notin S$ because $S\subseteq U$. Thus the total is the old sum plus the sum of these differences. Distributing the sum over subtraction and applying the induction hypothesis to both functions reduces this expression to $g(U)+g(\{i\}\cup U)-g(U)=g(U')$.

**Key facts.** `BooleanAnalysis.Hypercontractivity.signedIntersectionEnergy_insert`.
