<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/QuadraticPCPP.lean :: FABL.linearizedQuadraticSystemCharacterTester_close_of_acceptanceProbability_ge -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Closeness from High Tester Acceptance

**Claim.** If the linearized-system character tester accepts with probability at least $1-\varepsilon/2$, then some vector satisfying every equation of the system defines a linear function within relative Hamming distance $\varepsilon$ of the tested function.

**Proof.** Split into whether the system has a satisfying vector. If it does, encode the tested function by signs; the sign-encoded tester has the same acceptance probability (`f₂FunctionTesterOfSign_acceptanceProbability`). Since $0\le\varepsilon\le1$, the number $\varepsilon/2$ also lies in $[0,1]$, and the assumed acceptance bound meets the local tester theorem with rate $1$ and error parameter $\varepsilon/2$. The local tester guarantee (`IsLocalTester.close_of_acceptanceProbability_ge`), applied to the affine character tester (`affineCharacterFunctionTester_isLocalTester`), gives a nearby affine frequency character. Its frequency vector $a$ satisfies the linearized system, by the equivalence between system solutions and membership in the associated binary affine subspace (`satisfiesLinearized_iff_mem_binaryAffineSubspace`). The character representation identifies the nearby character with the sign encoding of the linear function $x\mapsto a\cdot x$. Sign encoding preserves relative Hamming distance (`relativeHammingDist_signEncode`), so the distance is at most $\varepsilon/2$, hence at most $\varepsilon$.

If the system has no satisfying vector, the tester always rejects and has acceptance probability zero (`alwaysRejectF₂CubeFunctionTester_acceptanceProbability`). But the assumed lower bound is $1-\varepsilon/2\ge1/2$, a contradiction. Thus the satisfiable case applies.

**Key facts.** `FABL.f₂FunctionTesterOfSign_acceptanceProbability`, `FABL.IsLocalTester.close_of_acceptanceProbability_ge`, `FABL.affineCharacterFunctionTester_isLocalTester`, `FABL.satisfiesLinearized_iff_mem_binaryAffineSubspace`, `FABL.relativeHammingDist_signEncode`, `FABL.alwaysRejectF₂CubeFunctionTester_acceptanceProbability`.
