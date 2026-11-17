<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZeroPRun.lean :: Randomized.PIT.pairFstD_gStep -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First projection invariance

**Claim.** For every bit string $D$, one gate-processing step preserves its first decoded component: the first component extracted from $gStep(D)$ equals the first component extracted from $D$.

**Proof.** Unfold the definition of the step and split according to its two Boolean conditions. If the state is done, the step returns $D$ itself. In either remaining branch, the new state is encoded as a pair whose first component is $sCtx(D)$. Decoding the first component of a pair encoding recovers that component, and $sCtx(D)$ is defined to be the first component extracted from $D$. Thus all branches give the claimed equality.
