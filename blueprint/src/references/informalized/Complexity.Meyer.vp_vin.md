<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerVerifierGlue.lean :: Complexity.Meyer.vp_vin -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Recovery of the Final String

**Claim.** For any bit strings $x,U,t,a,j,p$, applying the total second projection three times to $\langle\langle x,U\rangle,\langle\langle t,a\rangle,\langle j,p\rangle\rangle$ returns $p$.

**Proof.** The second projection of the outer pair is $\langle\langle t,a\rangle,\langle j,p\rangle\rangle$. Its second projection is $\langle j,p\rangle$, and the second projection of that pair is $p$. Each parsing succeeds because the encoding includes the separator after the doubled first component; therefore the total projection never uses its empty-string default.
