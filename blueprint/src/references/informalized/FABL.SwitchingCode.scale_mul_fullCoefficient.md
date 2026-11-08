<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/HastadSwitching.lean :: FABL.SwitchingCode.scale_mul_fullCoefficient -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Scaled full coefficient identity

**Claim.** For natural numbers $w$ and $i$, scaling the full coefficient by $(9w/4)^i$ gives $(w^i/i!)(2^i-1)$.

**Proof.** Expand the full coefficient and rewrite $9w/4=w(9/4)$. The powers $(9/4)^i$ and $(4/9)^i$ cancel, leaving $w^i(2^i-1)/i!$. Rearranging yields the stated expression.
