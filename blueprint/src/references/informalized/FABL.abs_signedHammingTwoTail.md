<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/GaussianSharpLevelOneCounterexample.lean :: FABL.abs_signedHammingTwoTail -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Absolute Value of the Signed Two-Tail Function

**Claim.** For $t\ge 0$, the absolute value of the difference between the upper-tail indicators at $x$ and at $-x$ equals their sum.

**Proof.** Negating $x$ negates its normalized Rademacher sum (`normalizedRademacherSum_neg_counterexample`). First suppose the sum at $x$ is greater than $t$. Since $t\ge0$, its negative is at most $0\le t$, so the sum at $-x$ cannot also exceed $t$. Thus the two indicators are $1$ and $0$, and the absolute value of their difference equals their sum. If the sum at $x$ does not exceed $t$, split into two cases: if the sum at $-x$ exceeds $t$, the indicators are $0$ and $1$; otherwise they are both $0$. In either case the absolute value of their difference again equals their sum.

**Key facts.** `FABL.normalizedRademacherSum_neg_counterexample`.
