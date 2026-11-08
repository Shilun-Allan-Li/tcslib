<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Noise/BlockCharacteristic.lean :: BooleanAnalysis.GaussianSpace.cos_sub_one_eq_sinc -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cosine and sinc identity

**Claim.** For every real $t$, $\cos t-1=-\frac{t^2}{2}\,\operatorname{sinc}(t/2)^2$.

**Proof.** First use the identity $\sin u=u\operatorname{sinc}(u)$, which holds at $u=0$ by the values of sine and sinc, and for $u\ne0$ by the definition of sinc. The double-angle formula, with $u=t/2$, gives $\cos t=1-2\sin(t/2)^2$. Substituting $\sin(t/2)=(t/2)\operatorname{sinc}(t/2)$ into this expression and simplifying yields the claimed identity.
