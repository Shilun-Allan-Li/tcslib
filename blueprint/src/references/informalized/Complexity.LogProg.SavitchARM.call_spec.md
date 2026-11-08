<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/SavitchARM/Recursion.lean :: Complexity.LogProg.SavitchARM.call_spec -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Recursive Reachability Call Specification

**Claim.** For every level $i\le w$, any state satisfying the level-$i$ invariant admits a finite safe execution to the return label whose Boolean records level-$i$ reachability, with only the midpoint register changed.

**Proof.** Proceed by induction on $i$. At level zero, choose the existing midpoint: it is within the bound by the invariant, and the required execution is exactly the base-level simulation (`Complexity.LogProg.SavitchARM.base_spec`). For the successor level $i+1$, the induction hypothesis supplies the recursive-call specification at level $i$. The invariant gives the global register bound (`Complexity.LogProg.SavitchARM.Inv.bd`). Reset the midpoint to zero, preserving the invariant (`Complexity.LogProg.SavitchARM.Inv.setM`), and apply the midpoint-loop specification with $k=2^w$: it returns some bounded midpoint and a Boolean expressing that there is an $m$ in the full range $0\le m<2^w$ for which both level-$i$ reachability legs hold (`Complexity.LogProg.SavitchARM.loop_spec`). This existential condition is precisely the defining clause for level-$i+1$ reachability; the loop’s lower bound $0\le m$ adds no restriction. The program first takes its recursive-entry steps from $\mathrm{cl}$ to the loop. They are legal because the current level is the successor level, hence nonzero, and the bounded-step principle (`Complexity.LogProg.SavitchARM.step_of`) prepends them to the loop execution while preserving the safety bound and the returned configuration.

**Key facts.** `Complexity.LogProg.SavitchARM.base_spec`, `Complexity.LogProg.SavitchARM.Inv.bd`, `Complexity.LogProg.SavitchARM.Inv.setM`, `Complexity.LogProg.SavitchARM.loop_spec`, `Complexity.LogProg.SavitchARM.step_of`.
