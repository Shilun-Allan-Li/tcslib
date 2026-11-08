<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/JohnsonLindenstrauss/UnionBound.lean :: JLDistortion.of_not_bad -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Distortion from a Controlled Difference

**Claim.** If $u-v$ does not trigger the bad distortion event for $A$, then the images of $u$ and $v$ satisfy the stated two-sided squared-norm distortion bound.

**Proof.** Write $w=u-v$. The failure of the bad-event inequality says
\[
\bigl|\,\|Aw\|^2-\|w\|^2\,\bigr|\le \varepsilon\|w\|^2.
\]
By linearity, $Aw=Au-Av$. The absolute-value bound gives both $\|Au-Av\|^2-\|u-v\|^2\le \varepsilon\|u-v\|^2$ and its reverse, which rearrange to the desired upper and lower bounds. The nonnegativity of the squared norms ensures the inequalities used in this rearrangement.
