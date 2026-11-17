<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/CoalitionalInfluenceAsymptotics.lean :: FABL.mean_bribeFunction_tribes_one_sub_mean_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Tribes Mean Gain Bound

**Claim.** For positive $w$ and natural number $s$, bribing any coordinate set $J$ to $+1$ increases the mean of the tribes function by at most $2|J|/2^w$.

**Proof.** Induct on the finite set $J$. For $J=\varnothing$, bribing changes nothing, so the gain is zero. For the inductive step, write the set as $\{i\}\cup J$, with $i\notin J$. Since the tribes function is monotone (FABL.tribes_monotone), the mean after bribing this additional coordinate equals the previous mean plus the Boolean influence of coordinate $i$ in the already bribed function (FABL.mean_bribeFunction_insert_one). That influence is at most $2^{-(w-1)}$ (FABL.booleanInfluence_bribeFunction_tribes_le), which equals $2\cdot 2^{-w}$ for $w>0$ (FABL.two_mul_inv_two_pow_eq_inv_pred_pow). By the induction hypothesis, the earlier bribes contribute at most $2|J|/2^w$. Adding the new-coordinate bound and using $|\{i\}\cup J|=|J|+1$ gives the claimed bound.

**Key facts.** `FABL.bribeFunction_empty`, `FABL.tribes_monotone`, `FABL.mean_bribeFunction_insert_one`, `FABL.booleanInfluence_bribeFunction_tribes_le`, `FABL.two_mul_inv_two_pow_eq_inv_pred_pow`.
