<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerVerifierGlue.lean :: Complexity.Meyer.vj_vin -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Recovering the Index String

**Claim.** For arbitrary bit strings $x,U,t,a,j,p$, applying the total second projection twice and then the total first projection to the nested encoding $\langle\langle x,U\rangle,\langle\langle t,a\rangle,\langle j,p\rangle\rangle$ recovers $j$.

**Proof.** Each encoded pair can be parsed at its separator: the doubled bits reproduce the first component, and the suffix after the separator is the second component. Thus the first second projection returns $\langle\langle t,a\rangle,\langle j,p\rangle\rangle$, the next returns $\langle j,p\rangle$, and the first projection of that pair is $j$. All parses succeed, so the total projections' failure defaults are not used.
