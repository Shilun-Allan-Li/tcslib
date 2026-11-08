<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Applications/SmallSetExpansion.lean :: BooleanAnalysis.Hypercontractivity.setIndicator_le_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Upper bound for a finite-set indicator

**Claim.** For any finite subset $A\subseteq\{0,1\}^n$ and any $x\in\{0,1\}^n$, the indicator satisfies $\mathbf 1_A(x)\le1$.

**Proof.** If $x\in A$, the indicator takes the value $1$. If $x\notin A$, it takes the value $0$. In either case its value is at most $1$.
