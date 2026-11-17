<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/RandomVariables/General.lean :: BooleanAnalysis.Hypercontractivity.mean_zero_hypercontractive -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Hypercontractivity from a Symmetric Extension

**Claim.** If $X$ has mean zero, unit second moment, finite $q$-moment for $q>2$, and $q$-norm $C>0$, then $X$ is $(2,q,1/(2C\sqrt{q-1}))$-hypercontractive.

**Proof.** Let $\nu$ be the law of $X$, and let $R$ be the uniform law on $\{-1,1\}$. On the product space with law $S=\nu\times R$, define $Z(x,y)=yx$. The sign symmetry of $R$ makes the transformation $(x,y)\mapsto(x,-y)$ preserve $S$ and send $Z$ to $-Z$, so $Z$ is symmetric. Since $y^2=1$, the $q$-norm and second moment of $Z$ agree with those of $X$; its mean is also zero. Thus the symmetric hypercontractivity theorem ( `symmetric_hypercontractive`) applies to $Z$, giving parameters $(2,q,\rho)$ with $\rho=1/(C\sqrt{q-1})$. In particular, for all real $a,b$, it bounds the $q$-norm of $a+\rho bZ$ by the $2$-norm of $a+bZ$. The sign variable $y$ is an independent Rademacher variable, and $t=\rho b\,x$ has mean zero. The randomization inequality (`randomization_norm_le`) therefore bounds the $q$-norm of $a+(1/2)t$ by that of $a+yt$. Rewriting these functions as $a+(\rho/2)b x$ and $a+\rho bZ$, respectively, then applying the symmetric hypercontractive bound yields the required estimate on the product space. Finally, the first coordinate has law $\nu$, and the product-space functions involving that coordinate have the same norms as the corresponding functions of $X$; hence the estimate transfers back to $X$. The parameter $\rho/2$ is nonnegative and less than one because $0\le\rho<1$, as supplied by the symmetric theorem. Also $2\le q$, and the required $q$-integrability is assumed, so all defining conditions of hypercontractivity hold.

**Key facts.** `BooleanAnalysis.Hypercontractivity.symmetric_hypercontractive`, `BooleanAnalysis.Hypercontractivity.randomization_norm_le`.

**Caveat.** The informal statement in the payload describes a different result; this account follows the supplied formal statement and proof.
