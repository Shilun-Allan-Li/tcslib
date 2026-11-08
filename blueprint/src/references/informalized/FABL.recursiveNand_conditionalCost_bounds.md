<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeExercises.lean :: FABL.recursiveNand_conditionalCost_bounds -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Conditional NAND Cost Bounds

**Claim.** Let $F_0=T_0=1$, $F_{d+1}=2T_d$, and $T_{d+1}=F_d+T_d/2$, and let $\rho=(1+\sqrt{33})/4$. For every natural number $d$, $F_d\le (2/\rho)\rho^d$ and $T_d\le \rho^d$.

**Proof.** Use induction on $d$, proving both bounds together. At $d=0$, the two costs and $\rho^0$ are all $1$; the false-cost bound follows from $1\le 2/\rho$, which follows from positivity of $\rho$ and its defining quadratic relation $\rho^2=\rho/2+2$ (`nandGrowthRate_pos`, `nandGrowthRate_sq`). For the induction step, nonnegativity of $\rho^d$ allows the inequalities to be multiplied by positive constants. The false-cost recurrence gives $F_{d+1}=2T_d\le2\rho^d=(2/\rho)\rho^{d+1}$. For the true cost, the recurrences and induction bounds give $T_{d+1}\le (2/\rho)\rho^d+\rho^d/2=\rho^d(2/\rho+1/2)$. The identity $2/\rho+1/2=\rho$ (`two_div_nandGrowthRate_add_half`) makes this at most the desired bound, in fact equal to $\rho^{d+1}$.

**Key facts.** `FABL.nandGrowthRate_pos`, `FABL.nandGrowthRate_sq`, `FABL.recursiveNandFalseCost_zero`, `FABL.recursiveNandFalseCost_succ`, `FABL.recursiveNandTrueCost_succ`, `FABL.two_div_nandGrowthRate_add_half`.
