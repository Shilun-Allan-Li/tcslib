<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeInequalities.lean :: FABL.disagreementIndicator_triangle -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Triangle Inequality for Disagreement Indicators

**Claim.** For real numbers $a,b,c$, the indicator of $a\ne c$ is at most the sum of the indicators of $a\ne b$ and $b\ne c$.

**Proof.** If $a=c$, the left side is $0$, so the inequality holds because both indicators on the right are nonnegative. If $a\ne c$, then $a=b$ and $b=c$ cannot both hold, since together they would imply $a=c$. At least one of the two right-hand indicators is therefore $1$, making their sum at least the left side, which is $1$.
