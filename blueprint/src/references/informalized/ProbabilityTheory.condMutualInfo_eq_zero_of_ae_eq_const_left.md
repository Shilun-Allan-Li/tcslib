<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/Entropy/Basic.lean :: ProbabilityTheory.condMutualInfo_eq_zero_of_ae_eq_const_left -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Vanishing with a constant first variable

**Claim.** If $X=c$ almost everywhere, then the conditional mutual information $I[X:Y\mid Z;\mu]$ is zero.

**Proof.** The characterization of zero conditional mutual information identifies it with conditional independence of $X$ and $Y$ given $Z$ (`condMutualInfo_eq_zero`). Conditional independence can be checked separately on each fiber $Z=z$ (`condIndepFun_iff` and the countable-fiber criterion `ae_iff_of_countable`). On any such fiber, the conditional measure is absolutely continuous with respect to the original measure, so the almost-everywhere equality $X=c$ remains true there. A constant random variable is independent of every random variable under any measure (`indepFun_const_left`); replacing that constant by the almost-everywhere equal $X$ preserves independence (`IndepFun.congr`). Thus $X$ and $Y$ are independent on every conditioning fiber, establishing conditional independence and therefore vanishing conditional mutual information.
