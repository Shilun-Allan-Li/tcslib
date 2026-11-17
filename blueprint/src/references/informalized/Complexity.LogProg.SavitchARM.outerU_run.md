<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/SavitchARM/Search.lean :: Complexity.LogProg.SavitchARM.outerU_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Outer Source Search

**Claim.** Assume $s\le w$. Given $u+k=2^w$ and $M\le 2^w$, the machine started at the outer source-search label from the specified outer state halts with the stated Boolean answer, while respecting the register bound and precondition throughout the run.

**Proof.** Proceed by induction on the number $k$ of source codes remaining. If $k=0$, then $u=2^w$, so the machine's initial comparison at the outer source-search label takes the rejecting branch. No candidate $u'$ can satisfy $u\le u'<2^w$, so the claimed answer is false. The outer-state register bound supplies the guard at the initial configuration, and the halt step preserves the required guarded-run condition. For the successor case, $u<2^w$. The machine first checks whether $u=2^w$; since this is false, it queries the initial-code oracle at $u$. If that query accepts, the target-search result (`outerV_run`) combines the search over targets from $0$ with the induction hypothesis for the next source $u+1$. The logical split behind this combination is that any successful source $u'\ge u$ either equals $u$ or is at least $u+1$; the former contributes the target-search answer and the latter the induction answer. If the query rejects, no witness can use $u$ as its source, so `exists_shift` justifies shifting the existential source search from $u$ to $u+1$, and the induction hypothesis gives the answer. In both branches, each transition is guarded using the outer-state register bound; the virtual oracle input is the required encoded pair by `vword_whole₂`, and the register identities identify the source and radius values used in that query.

**Key facts.** `Complexity.LogProg.AHalt.step`, `Complexity.LogProg.AHalt.ret`, `Complexity.LogProg.SavitchARM.gb_of`, `Complexity.LogProg.SavitchARM.outerSt_bd`, `Complexity.LogProg.SavitchARM.outerSt_U`, `Complexity.LogProg.SavitchARM.outerSt_K`, `Complexity.LogProg.SavitchARM.outerSt_s`, `Complexity.LogProg.vword_whole₂`, `Complexity.LogProg.SavitchARM.outerV_run`, `Complexity.LogProg.SavitchARM.exists_shift`.
