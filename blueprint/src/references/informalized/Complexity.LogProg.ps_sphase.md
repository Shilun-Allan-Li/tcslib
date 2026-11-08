<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathWalkProof.lean :: Complexity.LogProg.ps_sphase -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Existential phase search

**Claim.** Starting at the existential-search stage, the program terminates within the register bound and accepts exactly when some $j<n$ has the specified doubled-block encoding and satisfies $K(j)$.

**Proof.** The program first guesses a value $j$ by incrementing the source register from zero up to, but not including, the bound in the vertex-count register. The finite-guess principle for this loop (`nsem_guess`) identifies its accepting condition with the existence of such a $j$ for which the continuation accepts. For each guessed value, the program copies $j$ into the scratch register while preserving the source (`nsem_copy`). It then scans the binary word of that copy: the doubled-word scan theorem (`ps_scmp`) says this continuation accepts exactly when that word, with each bit doubled and followed by $01$, occurs at the prescribed pointer and the next stage accepts. The hypothesis supplies precisely that next-stage behavior, with source $j$ and the pointer advanced past the encoding. Combining the guessed-value condition with the copy and scan conditions yields the claimed existential statement. The initial source value is zero, so the lower bound in the guess loop is automatic; the register bounds and pointer allowance ensure each loop and scan stays within the bound.

**Key facts.** `Complexity.LogProg.nsem_guess`, `Complexity.LogProg.nsem_copy`, `Complexity.LogProg.ps_scmp`, `Complexity.LogProg.NSem.congr`, `Complexity.LogProg.PReg.reg`, `Complexity.LogProg.PReg.v_1`, `Complexity.LogProg.PReg.v_4`, `Complexity.LogProg.PS.of_eq`, `Turing.length_bits_le_self`.
