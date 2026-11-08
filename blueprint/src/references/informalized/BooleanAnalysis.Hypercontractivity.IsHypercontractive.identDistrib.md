<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/RandomVariables/Basic.lean :: BooleanAnalysis.Hypercontractivity.IsHypercontractive.identDistrib -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Hypercontractivity Under Identical Distribution

**Claim.** If $X$ and $Y$ are identically distributed and $X$ is $(p,q,\rho)$-hypercontractive, then $Y$ is $(p,q,\rho)$-hypercontractive.

**Proof.** Unpack the hypercontractivity assumptions for $X$. Identical distribution transfers the $L^q$ membership of $X$ to $Y$. For any real $a,b$, apply the same distributional equality to the measurable functions $x\mapsto a+\rho b x$ and $x\mapsto a+b x$. Their corresponding $q$- and $p$-norms for $Y$ therefore equal those for $X$. The desired norm inequality for $Y$ is now exactly the one assumed for $X};$ the numerical parameter conditions are unchanged.
