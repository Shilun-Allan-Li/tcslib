<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/RandomVariables/FiniteLaw.lean :: BooleanAnalysis.Hypercontractivity.FiniteLaw.finite_law_integral -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Integral under a finite law

**Claim.** If a measurable real-valued random variable takes values in a finite set almost everywhere on a finite measure space, then the integral of any function of that variable is the sum of its values on the finite set, weighted by the measures of the corresponding level sets.

**Proof.** Push the measure forward by $X$. The image measure is supported on $s$ almost everywhere, so restricting it to $s$ leaves it unchanged. Consequently, $f$ is integrable for this image measure: on the finite set its restriction is integrable. The change-of-variables formula for the measure pushforward identifies the original integral of $f(X)$ with the integral of $f$ against the image measure. Restricting that integral to $s$ and integrating over a finite set gives the sum of $f(x)$ times the real mass of each singleton. By the definition of the pushforward measure, the mass of the singleton $\{x\}$ is the mass of the event $X=x$, which yields the formula.
