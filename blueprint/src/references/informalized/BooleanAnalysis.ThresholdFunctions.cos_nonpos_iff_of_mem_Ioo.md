<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/GaussianPolar.lean :: BooleanAnalysis.ThresholdFunctions.cos_nonpos_iff_of_mem_Ioo -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cosine sign on a centered period

**Claim.** If $-\pi<\theta<\pi$, then $\cos\theta\le0$ if and only if $\theta\le-\pi/2$ or $\pi/2\le\theta$.

**Proof.** If neither inequality holds, then $-\pi/2<\theta<\pi/2$, where cosine is positive; this rules out $\cos\theta\le0$. For the converse, if $\theta\le-\pi/2$, then $\pi/2
e\!\!\!\!$—equivalently, $-\theta\ge\pi/2$—and the range condition gives $-\theta<\pi$, so cosine is nonpositive there; evenness yields $\cos\theta\le0$. If $\theta\ge\pi/2$, the same nonpositivity follows directly on $[\pi/2,\pi)$.
