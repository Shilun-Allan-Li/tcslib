<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingAsymptotics.lean :: FABL.factorialStirlingApprox_three_ratio_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Threefold Stirling Ratio

**Claim.** For every positive integer $d$, $S(3d)^2/S(d)^6=\frac{3}{4\pi^2}\frac{3^{6d}}{d^2}$.

**Proof.** Write $x=d/e$, so that $3d/e=3x$. In the ratio, the powered terms contribute $(3x)^{6d}/x^{6d}=3^{6d}$. The square-root terms simplify using $(\sqrt{6d\pi})^2=6d\pi$ and $(\sqrt{2d\pi})^6=(2d\pi)^3$. Their ratio is $6d\pi/(2d\pi)^3=3/(4\pi^2d^2)$. Multiplying these contributions yields the stated identity.
