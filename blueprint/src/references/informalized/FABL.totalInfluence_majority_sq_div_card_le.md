<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/ArrowLevelOneBound.lean :: FABL.totalInfluence_majority_sq_div_card_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Majority Influence Square Bound

**Claim.** For every positive $n$, the square of majority's total influence, divided by $n$, is at most $2/\pi+3/n$.

**Proof.** Split into even and odd dimensions. In the even case, write $n=2m+2$ and set $M=2m+1$, so $n=M+1$. The even-majority decomposition expresses the influence as $c\sqrt M+e$, where $c=\sqrt{2/\pi}$ and the odd error satisfies $0\le e\le1/\sqrt M$ (`FABL.totalInfluence_evenMajority_eq_odd_main_add_error`, `FABL.majority_isMajorityFunction`, and `FABL.oddMajorityTotalInfluenceError_mem_Icc`). Since $c\le1$, we have $\sqrt M e\le1$ and $c\sqrt M e\le1$; also $e^2\le1$. Squaring the decomposition and using $c^2=2/\pi$ and $n=M+1$ gives the stated bound. In the odd case, write $n=2m+1$. The squared influence divided by the dimension equals the level-one Fourier weight (`FABL.totalInfluence_majority_odd_sq_div_card`). This weight is at most $2/\pi+2/(\pi n)$ (`FABL.fourierWeightAtLevel_one_majority_odd_le`), which is at most $2/\pi+3/n$ because $\pi>3$.

**Key facts.** `FABL.totalInfluence_evenMajority_eq_odd_main_add_error`, `FABL.majority_isMajorityFunction`, `FABL.oddMajorityTotalInfluenceError_mem_Icc`, `FABL.totalInfluence_majority_odd_sq_div_card`, `FABL.fourierWeightAtLevel_one_majority_odd_le`.
