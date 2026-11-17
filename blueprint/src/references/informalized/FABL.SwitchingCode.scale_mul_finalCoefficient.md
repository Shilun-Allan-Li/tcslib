<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/HastadSwitching.lean :: FABL.SwitchingCode.scale_mul_finalCoefficient -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Scaled coefficient identity

**Claim.** For natural numbers $w$ and $i$, the scaled sum of the full coefficient and remainder equals $(w^i/i!)2^i$.

**Proof.** Expand the two coefficient definitions. Rewrite $9w/4$ as $w(9/4)$, so its $i$th power contributes $w^i(9/4)^i$. The factors $(9/4)^i$ and $(4/9)^i$ multiply to $1$. The remaining coefficient terms combine as $(2^i-1)+1=2^i$, with the natural-number subtraction cast to the reals valid because $1\le 2^i$. Rearranging the factors gives the claimed identity.
