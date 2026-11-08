<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/ISCountMath.lean :: Complexity.LogProg.ISCount.gs_outer -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Outer-Stage Condition on the Reachable Set

**Claim.** Under the stated hypothesis that $B(t)$ holds exactly at nonreachable $t<K$, the recursive condition over $K$ stages holds exactly when every reachable element fails $\mathrm{Acc}$ and $\mathrm{Kont}$ holds at the reachable set's cardinality.

**Proof.** Apply the finite-set characterization (`gs_iff`) to the $K$ positions starting at zero. In the forward direction it gives a selected set $T$ in that interval. A selected position is reachable and fails $\mathrm{Acc}$. Conversely, if a position below $K$ is reachable, it must be selected: otherwise the condition on unselected positions gives $B$ there, and the hypothesis on $B$ says it is not reachable, a contradiction. Thus $T$ is exactly the reachable set. The characterization's terminal condition is consequently $\mathrm{Kont}$ at the cardinality of that set, and its selected-position condition gives failure of $\mathrm{Acc}$ throughout it. In the reverse direction, choose $T$ to be the reachable set. Reachable elements lie below $K$, so this is a subset of the interval of all positions. By assumption they fail $\mathrm{Acc}$. At any unselected position in the interval, nonmembership in the reachable set and the hypothesis on $B$ imply $B$. Finally the cardinality and terminal condition are exactly those asserted.

**Key facts.** `Complexity.LogProg.ISCount.gs_iff`, `Complexity.LogProg.ISCount.mem_ball`, `Complexity.LogProg.ISCount.Mem.lt`.
