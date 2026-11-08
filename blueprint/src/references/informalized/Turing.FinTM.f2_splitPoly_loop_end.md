<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_splitPoly_loop_end -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial loop termination configuration

**Claim.** For $q>0$, the unary Boolean machine starting in loop control at index $c$ reaches the halted configuration after the specified cost plus one step, with advance control at its last index and with $Cq^{c+1}$ true bits in the output.

**Proof.** Apply the loop-run result (`f2_catalogPoly_loop`) at the last loop index, with the work heads initially zero, no prior output, and the quotient parameters chosen so the current tape length is $q$. It gives the configuration in advance control at the next index after exactly the specified loop cost, with $q(Cq^c)$ true bits appended. The power identity $q(Cq^c)=Cq^{c+1}$ puts the output in the claimed form. One additional transition from advance control at its last index halts the machine; this transition leaves the tape contents, head positions, and output unchanged. Therefore the resulting configuration is the stated halted one.

**Key facts.** `Turing.FinTM.f2_catalogPoly_loop`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`.
