<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/Basic.lean :: BooleanAnalysis.ThresholdFunctions.mul_thresholdSign_self -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Threshold Sign Identity

**Claim.** For every real number $r$, multiplication by its threshold sign gives $r\sigma(r)=|r|$, where $\sigma(r)=1$ for $r\ge0$ and $\sigma(r)=-1$ for $r<0$.

**Proof.** Split into the two possible signs of $r$. If $r\ge0$, then $\sigma(r)=1$ and $|r|=r$, so the identity follows. If $r<0$, then $\sigma(r)=-1$ and $|r|=-r$, again giving the identity.
