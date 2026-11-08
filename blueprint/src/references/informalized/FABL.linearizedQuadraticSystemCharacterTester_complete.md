<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/QuadraticPCPP.lean :: FABL.linearizedQuadraticSystemCharacterTester_complete -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Completeness of the Character Tester

**Claim.** If $a$ satisfies every equation of $L$, then the linearized-system character tester for $L$ accepts $x\mapsto a\cdot x$ with probability exactly $1$.

**Proof.** The hypothesis supplies a solution, so the tester uses its affine-character branch. Converting its $[?]$-valued answers to $[?]$-valued answers preserves acceptance probability: the conversion identity for the binary tester (`f₂FunctionTesterOfSign_acceptanceProbability`) identifies this probability with that of the underlying affine-character tester on the sign encoding of $x\mapsto a\cdot x$. The tester's local characterization (`affineCharacterFunctionTester_isLocalTester`) says this probability is $1$ whenever the queried function's frequency belongs to the corresponding binary affine subspace. Finally, the equivalence between satisfying the linearized equations and membership in that affine subspace (`satisfiesLinearized_iff_mem_binaryAffineSubspace`) puts $a$ in the required subspace, using the given solution as its base point. Thus the tester accepts with probability $1$.

**Key facts.** `FABL.f₂FunctionTesterOfSign_acceptanceProbability`, `FABL.affineCharacterFunctionTester_isLocalTester`, `FABL.satisfiesLinearized_iff_mem_binaryAffineSubspace`.
