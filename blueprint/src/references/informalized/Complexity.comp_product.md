<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/QueryReshape.lean :: Complexity.comp_product -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Product-Loop Register Update

**Claim.** Under the stated register bounds, zero condition, and inequalities, the product-test loop reaches the product-clean state with phase flag false. Register 10 is set to its initial value $v_8$, register 7 becomes $v_7+(v_8-v_{10})v_{11}$, and every other register is unchanged; all earlier configurations are admissible and bounded by $B$.

**Proof.** Induct on the remaining difference $v_8-v_{10}$, generalizing the register vector. If the difference is zero, then $v_{10}=v_8$, so the test immediately enters the product-clean state. The requested update to register 10 is therefore an update to its existing value, and the added term in register 7 is zero. The one-step reachability principle (\texttt{AReach.single}) establishes this case.

For a positive difference, the test takes the branch that copies register 11 into the phase register 6, then adds that amount to register 7 by a scale loop, and increments register 10. The register-copy loop theorem (\texttt{registerCopy\_loop}) justifies the copy, and the register-scale loop theorem (\texttt{registerScale\_loop}) adds $v_{11}$ to register 7 while clearing register 6. The bound needed during these operations follows from $v_7+v_{11}+(v_8-v_{10}-1)v_{11}\le B$, which is the assumed total bound rewritten using the positive difference. After the increment, the remaining difference has decreased by one, and register 7 has increased by $v_{11}$; hence the inductive hypothesis yields the claimed final value. The updated registers remain bounded using \texttt{register\_update\_le}; all other initial hypotheses are preserved. Reachability transitivity (\texttt{AReach.trans}) concatenates the copy, scale, increment, and inductive runs, while \texttt{AReach.step} accounts for the initial branch instruction. At each starting configuration the instruction admissibility condition is provided by \texttt{comp\_preS}.

**Key facts.** `Complexity.LogProg.AReach.single`, `Complexity.LogProg.registerCopy_loop`, `Complexity.LogProg.registerScale_loop`, `Complexity.LogProg.register_update_le`, `Complexity.comp_preS`, `Complexity.LogProg.AReach.trans`, `Complexity.LogProg.AReach.step`.
