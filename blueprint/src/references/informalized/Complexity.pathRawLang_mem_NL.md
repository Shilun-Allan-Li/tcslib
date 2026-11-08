<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathWalkProof.lean :: Complexity.pathRawLang_mem_NL -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Raw path language is in NL

**Claim.** The language of raw encodings of directed graphs with designated vertices, where the target is reachable from the source, belongs to nondeterministic logarithmic space.

**Proof.** Use the established nondeterministic recognition procedure for the path-encoding predicate. For each input $x$, its semantic analysis supplies a nondeterministic computation with a polynomial bound and an acceptance condition equivalent to `PathAcc x` (`Complexity.LogProg.ps_start`, together with `Complexity.LogProg.NSem.decides`). The machine’s space bound is converted to the required input-length bound using `Complexity.LogProg.pathA_npreS` and the monotonicity of halting under weakening the space predicate (`Complexity.LogProg.NHalts.mono`). The regular languages used by the procedure meet the logspace requirements by `Complexity.LogProg.pathAs_mem`, so the general theorem converting such a procedure into an NL decider applies (`Complexity.LogProg.narm_decides_poly`). Finally, `Complexity.pathAcc_iff` identifies its acceptance condition with membership in the raw path language. Thus the raw path language is in NL.

**Key facts.** `Complexity.LogProg.pathAs_mem`, `Complexity.LogProg.ps_start`, `Complexity.LogProg.NSem.decides`, `Complexity.LogProg.pathA_npreS`, `Complexity.LogProg.NHalts.mono`, `Complexity.LogProg.narm_decides_poly`, `Complexity.pathAcc_iff`.
