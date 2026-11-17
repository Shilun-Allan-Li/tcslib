<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/FKNImprovement.lean :: FABL.twentyFiveDivEight_lt_logb_two_nine -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A logarithmic inequality

**Claim.** The rational number $25/8$ is strictly less than $\log_2 9$.

**Proof.** Since $\log 2>0$, it suffices to prove $(25/8)\log 2<\log 9$. The identity $\log 9=2\log 3$ reduces this to $25\log 2<16\log 3$. The bounds $\log 3>9/8$ and $\log 2<9/8$ imply $16\log 3>18$ and $25\log 2<225/8<18$, respectively. Hence $25\log 2<16\log 3$, and division by the positive number $\log 2$ proves the result.
