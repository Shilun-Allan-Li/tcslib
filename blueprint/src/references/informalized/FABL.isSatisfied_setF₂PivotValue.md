<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeF₂PolynomialLearning.lean :: FABL.isSatisfied_setF₂PivotValue -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Satisfaction After Pivot Solving

**Claim.** If the pivot coefficient is $1$, replacing the pivot value by the constant plus the sum of the other terms produces an assignment satisfying the equation.

**Proof.** Split the equation’s evaluation into the pivot coordinate and the sum over all other coordinates. Since the update changes only the pivot coordinate, the latter sum is unchanged. The pivot term is therefore the updated value itself, because its coefficient is $1$. Writing the unchanged sum as $T$, the evaluation becomes $T+(c+T)$. In characteristic two, addition is commutative and associative, and $T+T=0$, so this equals $c$, as required.
