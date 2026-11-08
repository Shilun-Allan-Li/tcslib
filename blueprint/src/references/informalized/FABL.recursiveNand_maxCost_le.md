<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeExercises.lean :: FABL.recursiveNand_maxCost_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Maximum Recursive NAND Cost Bound

**Claim.** With $\rho=(1+\sqrt{33})/4$, for every natural number $d$, the maximum of the depth-$d$ false-output and true-output costs is at most $(2/\rho)\rho^d$.

**Proof.** The conditional cost bounds give $F_d\le (2/\rho)\rho^d$ and $T_d\le\rho^d$. First, $\rho>0$ by the positivity of the square root and its defining expression (nandGrowthRate_pos). Also, $\rho\le 2$: using $(\sqrt{33})^2=33$ and $\sqrt{33}\ge0$, this inequality follows by elementary algebra. Hence $1\le 2/\rho$. Since $\rho^d\ge0$, we have $T_d\le\rho^d\le(2/\rho)\rho^d$. Together with the bound for $F_d$, this proves the claimed bound on their maximum (recursiveNand_conditionalCost_bounds).

**Key facts.** `FABL.nandGrowthRate_pos`, `FABL.recursiveNand_conditionalCost_bounds`.
