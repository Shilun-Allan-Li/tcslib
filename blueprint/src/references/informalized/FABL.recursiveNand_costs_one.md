<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeExercises.lean :: FABL.recursiveNand_costs_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Depth-One Recursive NAND Costs

**Claim.** For the sequences defined by $F_0=T_0=1$, $F_{d+1}=2T_d$, and $T_{d+1}=F_d+T_d/2$, the depth-one costs are $F_1=2$ and $T_1=3/2$.

**Proof.** At depth one, the defining recurrences give $F_1=2T_0=2\cdot 1=2$. They also give $T_1=F_0+T_0/2=1+1/2=3/2$. Thus both asserted values hold.
