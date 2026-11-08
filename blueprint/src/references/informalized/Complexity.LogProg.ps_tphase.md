<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathWalkProof.lean :: Complexity.LogProg.ps_tphase -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Existential target phase

**Claim.** The target phase terminates within the register bound and accepts exactly when some vertex index below the vertex count has the required binary substring and satisfies $K$.

**Proof.** The program guesses a target value $j$ between the initial target register value, which is zero, and the vertex count. The general guessing principle (`nsem_guess`) gives termination and makes acceptance equivalent to the existence of such a $j$ for which the continuation accepts. For each guessed $j$, the program copies it into the scratch register (`nsem_copy`) and enters the plain-block comparison phase. The comparison result is exactly the required substring condition together with $K(j)$, by `ps_tcmp` and the hypothesis `hK`; the register bounds needed for that call follow from the original bounds and the stated length bound. Finally, because the target starts at zero, the guessed range is precisely $j<[1mn[0m$. The resulting existential condition is therefore the one in the claim.

**Key facts.** `Complexity.LogProg.nsem_guess`, `Complexity.LogProg.PReg.reg`, `Complexity.LogProg.PReg.v_5`, `Complexity.LogProg.PReg.v_1`, `Complexity.LogProg.nsem_copy`, `Complexity.LogProg.ps_tcmp`, `Complexity.LogProg.PS.of_eq`, `Complexity.LogProg.NSem.congr`.
