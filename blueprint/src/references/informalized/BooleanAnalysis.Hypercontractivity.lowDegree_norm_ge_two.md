<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Applications/LowDegree.lean :: BooleanAnalysis.Hypercontractivity.lowDegree_norm_ge_two -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Low degree norm bound

**Claim.** If $f$ has degree at most $k$ and $q\ge2$, then $\|f\|_q\le (\sqrt{q-1})^k\|f\|_2$.

**Proof.** Set $r=\sqrt{q-1}$, so $r\ge1$. Apply the general one-function hypercontractive inequality with input exponent $2$, output exponent $q$, and noise parameter $1/r$. Its admissibility follows from $1/r\le\sqrt{(2-1)/(q-1)}$. The noise composition law gives $T_{1/r}T_r f=T_1f=f$: indeed, the multipliers compose to $1$, and the Walsh expansion identifies $T_1f$ with $f$. Thus the inequality yields $\|f\|_q\le\|T_rf\|_2$. Finally, the low-degree noise bound gives $\|T_rf\|_2\le r^k\|f\|_2$, proving the claim.

**Key facts.** `BooleanAnalysis.Hypercontractivity.general_one_function_hypercontractivity`, `BooleanAnalysis.Hypercontractivity.noiseOp_compose`, `BooleanAnalysis.walsh_expansion`, `BooleanAnalysis.Hypercontractivity.l2Norm_noiseOp_le`.
