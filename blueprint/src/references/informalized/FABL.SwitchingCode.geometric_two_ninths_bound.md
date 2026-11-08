<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/HastadSwitching.lean :: FABL.SwitchingCode.geometric_two_ninths_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Finite geometric sum bound

**Claim.** For every natural number $m$, the sum of the first $m$ powers of $2/9$ is at most $9/7$, including the empty sum when $m=0$.

**Proof.** Apply the finite geometric-sum identity to express the sum in terms of $1-(2/9)^m$, divided by $1-2/9=7/9$. Since $(2/9)^m$ is nonnegative, the numerator is at most $1$. Thus the sum is at most $1/(7/9)=9/7$.
