<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/AlgebraicPCPP.lean :: FABL.relativeHammingDist_signTwist -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sign Twisting Preserves Distance

**Claim.** Multiplying both sign-valued functions pointwise by the same phase function preserves their relative Hamming distance.

**Proof.** It is enough to show that the twist preserves the number of points where the functions differ, since the relative distance divides that number by the same domain size. For each $x$, the map sending a sign $a$ to $a\,\mathrm{phase}(x)$ is injective: multiplication by the common phase can be cancelled. Hence $f(x)$ and $g(x)$ differ exactly when their twists differ, and the mismatch counts—and thus the relative distances—are equal.
