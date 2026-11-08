<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerVerifierGlue.lean :: Complexity.Meyer.vD_vin -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Decoding the nested input

**Claim.** Applying the total second projection, then the total first projection, then the marker-dropping transducer to the nested encoding yields the result of applying that transducer to $U$.

**Proof.** By definition, the outer encoding pairs $\langle x,U\rangle$ with the encoding containing $t,a,j,p$. Decoding this outer pair and taking its second component recovers that inner encoding; taking its first component then recovers $U$. These recoveries hold because decoding the encoding of any two strings returns that pair. Applying the marker-dropping transducer to the recovered string gives $\mathrm{dropMarker}(U)$, as claimed.
