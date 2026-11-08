<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/GaussianSharpLevelOneCounterexample.lean :: FABL.signedHammingTwoTail_mem_Icc -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Signed Two-Sided Tail Bounds

**Claim.** For every threshold $t$, natural number $n$, and sign vector $x$, the difference between the upper-tail indicator at $x$ and the upper-tail indicator at $-x$ lies in $[-1,1]$.

**Proof.** Each upper-tail indicator is either $0$ or $1$, according as the normalized sum does not exceed $t$ or is strictly greater than $t$. The difference of two such values has four possibilities: $0-0=0$, $0-1=-1$, $1-0=1$, and $1-1=0$. All lie in $[-1,1]$, as required.
