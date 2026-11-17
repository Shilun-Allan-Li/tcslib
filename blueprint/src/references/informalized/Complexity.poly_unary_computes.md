<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/TMSAT.lean :: Complexity.poly_unary_computes -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unary Polynomial Computation

**Claim.** For all $c,C\in\mathbb N$, the unary box-enumeration machine outputs $C(|x|+1)^{c+1}$ ones on input $x$ within $(C+5(c+1)+4)(|x|+1)^{c+1}$ steps.

**Proof.** Fix $x$ and set $q=|x|+1$. The loop theorem, applied at level $c$ with $r=q$ and initial marked-head position $0$, shows that after $\operatorname{polyCost}(q,C,c+1)$ steps the machine is in the final advance state with all heads reset and has output $Cq^{c+1}$ ones. Startup takes $2q$ steps; one further step from the final advance state halts. Run composition and the characterization of computation in time therefore give the required output and halting after $2q+\operatorname{polyCost}(q,C,c+1)+1$ steps. The cost bound gives $\operatorname{polyCost}(q,C,c+1)\le (C+1+5(c+1))q^{c+1}$. Since $q\le q^{c+1}$ and $1\le q^{c+1}$, the total is at most $(C+1+5(c+1)+3)q^{c+1}=(C+5(c+1)+4)q^{c+1}$. Monotonicity of the time bound extends the computation to the stated time.

**Key facts.** `Complexity.poly_loop`, `Complexity.poly_start`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.MultiTapeTM.runFrom_add`, `Turing.FinTM.computesInTime_iff`, `Complexity.polyCost_le`, `Turing.FinTM.ComputesInTime.mono`.
