<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/KKLBribery.lean :: FABL.briberySetsTo_odds_invariant -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bribery-Set Odds Invariant

**Claim.** Let $n\ge2$, and let $f$ be monotone with positive bias $p$. For any target $q<1$, the recursively defined bribery sets satisfy $(1+2r)^{|J_t|}p(1-p_t)\le p_t(1-p)$ for every $t\ge0$, where $r=\frac{\log n}{100n}$ and $p_t$ is the bias after bribing the coordinates in $J_t$.

**Proof.** Write $J_t$ for the set after $t$ steps, $p_t$ for the bias of the function obtained by setting its coordinates to $1$, and $R=1+2r$. We induct on $t$. At $t=0$, the set is empty and the bribed function is the original function, so the inequality reduces to equality.

Suppose the assertion holds at stage $t$. If the mean at that stage is already at least the target, the procedure leaves the set unchanged, so the induction hypothesis proves the next case as well. Consider instead the step where a coordinate is added. Let $J=J_t$, let $g$ be the function bribed on $J$, and let $i$ be its maximum-influence coordinate. Monotonicity implies that bribing the empty set and then the larger set $J$ cannot decrease the mean; together with the original positive bias, this shows that $g$ has positive bias. The condition that the current mean is below the target, combined with $q<1$, shows that this bias is less than $1$. Thus the maximum-influence coordinate is fresh, so adjoining it increases the set size by one.

The one-coordinate odds estimate for a monotone function says that after setting coordinate $i$ to $1$, its new bias $p'$ satisfies $R\,p_g(1-p')\le p'(1-p_g)$, where $p_g$ is the bias of $g$. This applies because $g$ is monotone and has bias strictly between zero and one. The fresh-coordinate identity identifies this new function with the one bribed on $J\cup\{i\}$. Multiply the estimate by the nonnegative factor $R^{|J|}p$, and multiply the induction hypothesis by the nonnegative new bias $p'$. Combining the resulting inequalities and rearranging factors gives $R^{|J|+1}p(1-p')\,p_g\le p'(1-p)\,p_g$. Since $p_g>0$, cancel it to obtain the desired invariant at stage $t+1$. The factors used here are nonnegative: $r>0$, and every bias lies in $[0,1]$.

**Key facts.** `FABL.briberySetsTo_succ`, `FABL.mean_bribeFunction_mono_set_one`, `FABL.bribeFunction_empty`, `FABL.positiveBias_eq_mean`, `FABL.maximumInfluenceCoordinate_fresh_of_bias`, `FABL.monotone_bribeFunction`, `FABL.positiveBias_odds_step`, `FABL.bribeFunction_insert`, `FABL.briberyRate_pos`, `FABL.positiveBias_mem_Icc`.
