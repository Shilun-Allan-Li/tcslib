<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/Frag.lean :: Complexity.LogProg.eqC_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Run Comparing Two Register Words

**Claim.** When the two registers contain words with a common prefix, the comparison run scans that prefix and either reaches the yes continuation if the words agree or the no continuation at their first differing bit, with both heads together at a position in the stated range.

**Proof.** Induct on the remaining suffix $u_1$. If it is empty, the first word ends at the current position. The comparison transition moves both heads right into the yes continuation when the second suffix is also empty; if the second suffix is nonempty, it enters the no continuation. In both cases the resulting common head position is $|pre|-1$, and the only earlier configuration is the initial one at position $|pre|$.

If $u_1$ begins with a bit $a$, the first register has bit $a$ at the current position. If $u_2$ is empty, the second register is blank there, so the machine enters the no continuation at position $|pre|-1$. If $u_2$ also begins with a bit $b$, compare them. When $a\ne b$, the machine immediately enters the no continuation at position $|pre|-1$. When $a=b$, it moves both heads right, staying in the comparison state, and the induction hypothesis applies to the extended common prefix $pre\,a$ and the two remaining suffixes. Prepending this step gives the required terminal state and position; the time-zero configuration and the inductively controlled later configurations satisfy the stated bounds on all earlier positions.

The reading lemmas `eqCfg_read₁` and `eqCfg_read₂` identify the two bits scanned at the common head position. The one-step run formula `rrun_one_eq` and the simultaneous-head movement formula `apply_mv2Act` determine the transition and new position. When the equal-bit case continues recursively, `rrun_add` concatenates the first step with that run.

**Key facts.** `Complexity.LogProg.eqCfg_read₁`, `Complexity.LogProg.eqCfg_read₂`, `Complexity.LogProg.rrun_one_eq`, `Complexity.LogProg.apply_mv2Act`, `Complexity.LogProg.rrun_add`.
