<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/PolyTimePairing.lean :: Complexity.polyTimeComputable_of_linear -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Linear-time computation implies polynomial time

**Claim.** If a finite binary Turing machine computes $f$ on every input in time $a(n+1)$ for some natural number $a$, then $f$ is polynomial-time computable.

**Proof.** Choose the machine and coefficient $a$ witnessing the assumed linear-time computation. The polynomial-time definition permits a bound $C(n+1)^c$; take $C=a$ and $c=1$. Since $(n+1)^1=n+1$, the given time bound is exactly this polynomial bound, so the same machine witnesses polynomial-time computability.
