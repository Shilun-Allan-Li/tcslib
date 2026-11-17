<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Applications/SmallSetExpansion.lean :: BooleanAnalysis.Hypercontractivity.setIndicator_sq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Idempotence of a finite-set indicator

**Claim.** For any finite subset $A\subseteq\{0,1\}^n$ and point $x\in\{0,1\}^n$, one has $\mathbf 1_A(x)^2=\mathbf 1_A(x)$.

**Proof.** If $x\in A$, then the indicator is $1$, whose square is itself. If $x\notin A$, it is $0$, whose square is also itself. These two cases establish the identity.
