<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/SharpLevelOneInequality.lean :: FABL.not_sharpLevelOneInequality_signed -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Failure of the Level-One Fourier Bound

**Claim.** There is a bounded real-valued function on a sign cube whose mean absolute value is $1/2$, but whose level-one squared Fourier weight exceeds the proposed bound.

**Proof.** Assume the proposed inequality holds for every dimension and every function satisfying its hypotheses. Apply it to the supplied signed counterexample in dimension two with $\alpha=1/2$. Its pointwise values lie in $[-1,1]$ (`FABL.sharpLevelOneSignedCounterexample_mem_Icc`), and its mean absolute value is $1/2$ (`FABL.mean_abs_sharpLevelOneSignedCounterexample`), so the assumed inequality applies. The counterexample's level-one Fourier weight is $1/2$ (`FABL.fourierWeightAtLevel_one_sharpLevelOneSignedCounterexample`). The bound would therefore imply $1/2\le (1/2)\log 2$, or $1\le\log 2$. But $\log 2<1$, a contradiction. Thus the universal inequality fails.

**Key facts.** `FABL.sharpLevelOneSignedCounterexample_mem_Icc`, `FABL.mean_abs_sharpLevelOneSignedCounterexample`, `FABL.fourierWeightAtLevel_one_sharpLevelOneSignedCounterexample`.
