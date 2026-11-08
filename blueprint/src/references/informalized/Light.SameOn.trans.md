<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Regions.lean :: Light.SameOn.trans -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Transitivity of agreement

**Claim.** If $\mu'$ agrees with $\mu$ and $\mu''$ agrees with $\mu'$ on every index satisfying $K$, then $\mu''$ agrees with $\mu$ on those indices.

**Proof.** At any index satisfying $K$, the two hypotheses give $\mu''(b)=\mu'(b)$ and $\mu'(b)=\mu(b)$. Transitivity of equality gives the required agreement.
