<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Cube/EvenMoments.lean :: BooleanAnalysis.Hypercontractivity.hypercontractivity_2_q -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Even-Exponent Hypercontractivity

**Claim.** For an even integer $q\ge2$, if $\rho^2\le1/(q-1)$, then the $q$th moment of the noise operator applied to $f$ is at most the $(q/2)$th power of the second moment of $f$.

**Proof.** Write the even integer as $q=2k$. Since $q\ge2$, we have $k\ge1$. The noise condition becomes $\rho^2\le1/(2k-1)$. Apply `hypercontractivity_2_2k` with this $k$ and constraint. Its left side is the $q$th moment, while its right side has exponent $k=q/2$, giving the claim.

**Key facts.** `BooleanAnalysis.Hypercontractivity.hypercontractivity_2_2k`.
