<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/RandomVariables/Sharp/Parameters.lean :: BooleanAnalysis.Hypercontractivity.SharpDiscrete.radius_pos_lt_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sharp radius bounds

**Claim.** If $q>2$ and $0<\lambda<1/2$, then $0<\rho(q,\lambda)<1$.

**Proof.** Put $u=\log((1-\lambda)/\lambda)$. Since $(1-\lambda)/\lambda>1$, we have $u>0$. Also $0<q/(q-1)<q$, so $u/q<u/(q/(q-1))$, and both arguments are positive. The hyperbolic sine is positive and strictly increasing on positive inputs. Thus the numerator and denominator in the ratio defining $\rho^2$ are positive, and the numerator is strictly smaller than the denominator. Consequently $0<\rho^2<1$, which gives $0<\rho<1$ upon taking square roots.
