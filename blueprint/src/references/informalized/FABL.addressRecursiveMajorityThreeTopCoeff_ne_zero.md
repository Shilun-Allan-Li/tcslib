<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveMajorityDecisionTrees.lean :: FABL.addressRecursiveMajorityThreeTopCoeff_ne_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonzero Majority Top Coefficient

**Claim.** For every depth $d\in\mathbb{N}$, the top correlation of the depth-$d$ recursively composed three-input majority function is nonzero.

**Proof.** Proceed by induction on the depth. At depth zero, the function is the single input sign, and its top coefficient is $1$, hence nonzero. For the step, the recurrence for the top coefficient gives the next coefficient as $-1/2$ times the cube of the current coefficient. The cube of a nonzero real number is nonzero, and multiplying by the nonzero factor $-1/2$ preserves nonvanishing. Thus the coefficient remains nonzero at every depth.

**Key facts.** `FABL.addressRecursiveMajorityThreeTopCoeff_succ`.
