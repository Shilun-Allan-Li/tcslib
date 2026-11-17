<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Applications/SmallSetExpansion.lean :: BooleanAnalysis.Hypercontractivity.setIndicator_rpow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positive powers of an indicator

**Claim.** For any finite subset $A\subseteq\{0,1\}^n$, point $x\in\{0,1\}^n$, and real $r>0$, one has $\mathbf 1_A(x)^r=\mathbf 1_A(x)$.

**Proof.** Split according to whether $x\in A$. If it is, the indicator equals $1$, and $1^r=1$. If it is not, the indicator equals $0$, and since $r>0$, the real power $0^r$ is $0$. Thus both cases give the claimed identity.
