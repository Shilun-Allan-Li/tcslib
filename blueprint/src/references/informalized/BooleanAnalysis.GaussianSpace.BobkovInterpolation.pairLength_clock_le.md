<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Bobkov/Interpolation.lean :: BooleanAnalysis.GaussianSpace.BobkovInterpolation.pairLength_clock_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Clock contribution bound

**Claim.** For every $c\ge 0$, the symmetric average length satisfies $L(t,c)\le \sqrt c+L(t,0)$.

**Proof.** Apply subadditivity of the square root ($\texttt{sqrt\_add\_le\_add\_sqrt}$) to each of the two radicands, separating off $c$. The remaining parts are nonnegative because they are sums of squares. Each square root at clock value $c$ is therefore at most $\sqrt c$ plus its corresponding square root at clock value zero. Averaging these two inequalities gives the claim.

**Key facts.** `BooleanAnalysis.GaussianSpace.BobkovInterpolation.sqrt_add_le_add_sqrt`.
