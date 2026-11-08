<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Applications/SmallSetExpansion.lean :: BooleanAnalysis.Hypercontractivity.setIndicator_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonnegativity of a finite-set indicator

**Claim.** For any finite subset $A\subseteq\{0,1\}^n$ and any $x\in\{0,1\}^n$, the indicator satisfies $0\le\mathbf 1_A(x)$.

**Proof.** If $x\in A$, the indicator takes the value $1$; otherwise it takes the value $0$. Both values are nonnegative.
