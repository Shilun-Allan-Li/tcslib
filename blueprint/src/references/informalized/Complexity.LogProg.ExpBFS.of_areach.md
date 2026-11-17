<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ExpBFS/Run.lean :: Complexity.LogProg.ExpBFS.of_areach -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lifting a Register Run to the Memory Machine

**Claim.** A guarded run of the deterministic register machine from $a$ to a nonhalting configuration $a'$ lifts to a memory-machine run from $(a,(M,p))$ to $(a',(M,p))$, with $G(x,B,P)$ holding throughout, provided $0\le p\le P$.

**Proof.** First use the lifting fact `MReach.of_areach`: a guarded deterministic register run whose endpoint is nonhalting is also a memory-machine run with the memory and head component fixed at $(M,p)$. This gives the register guard together with equality of the memory component to $(M,p)$ at every preceding configuration. Strengthen that guard to $G$ by retaining its register component and using the fixed head equality to identify the head position with $p$. The assumed inequalities $0\le p\le P$ then give the required head bounds. This strengthening is precisely the monotonicity principle for reachability (`MReach.mono`).

**Key facts.** `Complexity.LogProg.MReach.of_areach`, `Complexity.LogProg.MReach.mono`.
