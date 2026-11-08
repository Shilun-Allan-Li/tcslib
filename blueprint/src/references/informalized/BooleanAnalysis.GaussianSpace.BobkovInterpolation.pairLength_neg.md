<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Bobkov/Interpolation.lean :: BooleanAnalysis.GaussianSpace.BobkovInterpolation.pairLength_neg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evenness of symmetric average length

**Claim.** For every profile and parameters, $L(-t,c)=L(t,c)$.

**Proof.** Replacing $t$ by $-t$ interchanges the two terms in the symmetric average: the arguments $a+tb$ and $a-tb$ swap, as do the vector expressions $u+tv$ and $u-tv$. Their squared coordinate sums consequently swap as well. Since addition of the two square roots is unchanged by this interchange, the average is unchanged.
