<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathWalkProof.lean :: Complexity.LogProg.ps_unary -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unary-prefix phase

**Claim.** The unary-prefix phase terminates within the register bound and accepts exactly when there is an $n'[1m\ge\sigma.n[0m$ for which the specified doubled-bit pattern occurs and $K(n')$ holds.

**Proof.** Strengthen the claim by induction on the number of input positions remaining after the pointer. At the current position, the program reads the first bit and advances the pointer, then reads the next bit. If the pair is $01$, it has found the delimiter: the current index $[1m\sigma.n[0m$ itself is a valid candidate, and the hypothesis `hK` supplies $K([1m\sigma.n[0m)$. If the pair is $00$ or $10$, the delimiter and all required preceding pairs cannot match, so the program rejects. If the pair is $11$, it advances past both bits, increments the unary counter, and applies the induction hypothesis to the shorter remaining input. The hypothesis $p=2n$ ensures that these read positions are exactly $2n$ and $2n+1$ at each stage. The maintained conditions on all earlier pairs combine with the recursive condition to give `UnaryRest`; conversely, any valid endpoint must either be the current delimiter or lie after another $11$ pair. The input-bit oracle and `lt_of_getD_true` justify the reads and pointer bounds, while the semantic rules for oracle calls, increments, and rejection assemble the branches and preserve termination and register bounds.

**Key facts.** `Complexity.LogProg.NSem.call_neg`, `Complexity.LogProg.NSem.inc`, `Complexity.LogProg.NSem.ret`, `Complexity.LogProg.NSem.call_pos`, `Complexity.LogProg.PReg.reg`, `Complexity.LogProg.PReg.v_0`, `Complexity.LogProg.PS.of_eq`, `Complexity.LogProg.pathOr_bit`, `Complexity.lt_of_getD_true`.
