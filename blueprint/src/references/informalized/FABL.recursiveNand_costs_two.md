<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeExercises.lean :: FABL.recursiveNand_costs_two -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Maximum Recursive NAND Cost at Depth Two

**Claim.** For the sequences defined by $F_0=T_0=1$, $F_{d+1}=2T_d$, and $T_{d+1}=F_d+T_d/2$, the larger of $F_2$ and $T_2$ is $3$.

**Proof.** Using the depth-one values, $F_2=2T_1=3$ and $T_2=F_1+T_1/2=2+3/4=11/4$. Since $11/4<3$, their maximum is $3$.
