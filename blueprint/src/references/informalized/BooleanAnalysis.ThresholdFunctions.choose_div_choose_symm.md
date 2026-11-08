<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/Majority.lean :: BooleanAnalysis.ThresholdFunctions.choose_div_choose_symm -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Symmetry of Binomial Ratios

**Claim.** If $p+q=m$, then $\binom mq/\binom{2m}{2q}=\binom mp/\binom{2m}{2p}$ as real numbers.

**Proof.** The relation $p+q=m$ gives $q=m-p$. By symmetry of binomial coefficients, $\binom m{m-p}=\binom mp$. Also $2(m-p)=2m-2p$, so the same symmetry gives $\binom{2m}{2m-2p}=\binom{2m}{2p}$. Both numerator and denominator therefore agree with those in the right-hand ratio.
