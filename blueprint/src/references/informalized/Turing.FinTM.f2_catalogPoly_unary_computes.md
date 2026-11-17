<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_catalogPoly_unary_computes -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unary output computation

**Claim.** For every Boolean word $x$, the specified unary machine halts after $(C+5(c+1)+4)(|x|+1)^{c+1}$ steps and outputs exactly $C(|x|+1)^{c+1}$ copies of true.

**Proof.** Fix $x$ and put $q=|x|+1$. Apply the loop-phase result (`f2_catalogPoly_loop`) with index $c$, initial counter value $q$, and $r=q$, $j=0$. It shows that after the loop's prescribed cost, the machine is in the terminal advance state with output extended by $qCq^c=Cq^{c+1}$ true symbols. The initial-phase result (`f2_catalogPoly_start`) places the machine in the required loop configuration after $2q$ steps. One further transition from the final advance state halts without changing the output. By the run composition laws (`runFrom_add`, `runFrom_succ_eq_step'`), the total time is $2q+\mathrm{cost}(q,C,c+1)+1$, and the machine therefore computes the claimed output by `computesInTime_iff`. The cost estimate `f2_catalogPolyCost_le` bounds the loop cost by $(C+1+5(c+1))q^{c+1}$. Since $q\le q^{c+1}$ and $1\le q^{c+1}$, the initial and final overhead is absorbed, giving a time at most $(C+5(c+1)+4)q^{c+1}$. The time-monotonicity result `ComputesInTime.mono` extends computation to exactly the stated bound.

**Key facts.** `Turing.FinTM.f2_catalogPoly_loop`, `Turing.FinTM.f2_catalogPoly_start`, `Turing.FinTM.computesInTime_iff`, `Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.FinTM.f2_catalogPolyCost_le`, `Turing.FinTM.ComputesInTime.mono`.
