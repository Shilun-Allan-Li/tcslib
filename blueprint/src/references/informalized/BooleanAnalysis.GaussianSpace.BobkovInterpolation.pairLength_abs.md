<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Bobkov/Interpolation.lean :: BooleanAnalysis.GaussianSpace.BobkovInterpolation.pairLength_abs -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Symmetry under absolute displacement

**Claim.** The symmetric average length at displacement $|t|$ and parameter $c$ equals its value at displacement $t$ and parameter $c$.

**Proof.** If $t\ge0$, then $|t|=t$, so the equality is immediate. If $t\le0$, then $|t|=-t$; the symmetry of the average length under negating its displacement (`pairLength_neg`) gives the result.

**Key facts.** `BooleanAnalysis.GaussianSpace.BobkovInterpolation.pairLength_neg`.
