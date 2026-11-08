<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/Peres.lean :: FABL.peresMajorityUpperBound_sub_main_isBigO -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Peres Bound Asymptotic Remainder

**Claim.** As $\delta$ tends to $0$ through nonnegative values, the difference between the Peres majority upper bound at $\delta$ and $\sqrt{2/\pi}\,\sqrt{\delta}$ is $O(\delta^{3/2})$.

**Proof.** Near $0$ in the nonnegative half-line, the values of $\delta$ are nonnegative. The floor estimate for the reciprocal of $\lfloor 1/\delta\rfloor$ implies, after raising to the power $3/2$, that $(1/\lfloor 1/\delta\rfloor)^{3/2}=O(\delta^{3/2})$ (`one_div_natFloor_one_div_isBigO`). Also, the difference $\sqrt{1/\lfloor 1/\delta\rfloor}-\sqrt{\delta}$ is $O(\delta^{3/2})$ (`sqrt_one_div_natFloor_one_div_sub_sqrt_isBigO`). Multiplying these estimates by the fixed constants $\sqrt{2/\pi}$ and $4$, respectively, and adding them preserves the same order bound. Expanding the definition of the Peres upper bound identifies this sum with the stated difference.

**Key facts.** `FABL.one_div_natFloor_one_div_isBigO`, `FABL.sqrt_one_div_natFloor_one_div_sub_sqrt_isBigO`.
