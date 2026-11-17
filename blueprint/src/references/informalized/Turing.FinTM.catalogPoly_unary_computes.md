<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.catalogPoly_unary_computes -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unary Generator Time Bound

**Claim.** For all natural numbers $c,C$, the unary generator outputs $C(|x|+1)^{c+1}$ ones on each Boolean input $x$ within $(C+5(c+1)+4)(|x|+1)^{c+1}$ steps.

**Proof.** Fix an input $x$ and put $q=|x|+1$. The main loop result at level $c$, started with all heads at zero and with the counter head at $q$, shows that after `catalogPolyCost`$(q,C,c+1)$ steps the machine has entered the terminal advance state and output $q(Cq^c)=Cq^{c+1}$ ones. Startup reaches the required outermost loop configuration in $2q$ steps (`catalogPoly_start`); one further step from the terminal advance state halts without changing the output. The characterization of computation in time by halting state and output (`computesInTime_iff`) therefore gives computation in $2q+\text{catalogPolyCost}(q,C,c+1)+1$ steps.

The recursive cost estimate bounds this by $2q+(C+1+5(c+1))q^{c+1}+1$ (`catalogPolyCost_le`). Since $q\le q^{c+1}$ and $1\le q^{c+1}$, this is at most $(C+5(c+1)+4)q^{c+1}$. Monotonicity of the time bound then gives computation within the stated number of steps (`ComputesInTime.mono`).

**Key facts.** `Turing.FinTM.catalogPoly_loop`, `Turing.FinTM.catalogPoly_start`, `Turing.FinTM.computesInTime_iff`, `Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.FinTM.catalogPolyCost_le`, `Turing.FinTM.ComputesInTime.mono`.
