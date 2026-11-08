<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/InputAccess.lean :: Complexity.LogProg.indexedSeek_loop -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Indexed seek loop

**Claim.** The loop searches the interval of indices from the initial value of $\mathrm{idx}$ through the next $\mathrm{count}$ values. If $\mathrm{query}$ lies in this interval, it reaches `hit` with the pointer advanced by $\mathrm{stride}(\mathrm{query}-\mathrm{idx})$ and the index equal to $\mathrm{query}$; otherwise it reaches `miss` with the pointer at the initial limit and the index increased by $\mathrm{count}$. Every earlier configuration satisfies $\mathrm{PreS}$ and the register bound.

**Proof.** Proceed by induction on $\mathrm{count}$, allowing the register assignment to vary. When $\mathrm{count}=0$, the relation $v(\mathrm{limit})=v(\mathrm{ptr})$ follows from the pointer-limit equation. Since $v(\mathrm{idx})\le v(\mathrm{query})$, the query cannot be below $v(\mathrm{idx})$. Thus the test branches directly to `miss`; the pointer update to $v(\mathrm{limit})$ leaves the register assignment unchanged, and the one-step reachability fact gives the result.

For the successor case, the pointer-limit equation shows that there is room to advance the pointer by one stride without passing the limit. If $v(\mathrm{idx})=v(\mathrm{query})$, the test branches to `probe`, which branches to `hit`; neither register changes, so the stated hit endpoint is the initial configuration, as required.

Otherwise, the test proceeds to `probe`, which branches to `bump`. The bump increments the index, and the $\mathrm{stride}$ successive pointer increments return control to `test`. The register-update bound lemma ($\texttt{register\_update\_le}$) ensures that the index and pointer remain at most $B$ during these updates; the room estimate and the initial register bounds supply the needed bounds for the intermediate increments. The increment-chain lemma ($\texttt{arm\_increments}$) packages the pointer advances and their precondition and bound checks. Together these steps give a reachability segment from the original test configuration to a new test configuration with pointer increased by one stride and index increased by one.

Apply the induction hypothesis at that new test configuration, with the remaining count. Its pointer-limit equation follows by subtracting one stride from the original count, and its index and query inequalities follow from the single index increment and the register values being distinct. If the query is still in range, the induction endpoint agrees with the claimed hit endpoint: the extra stride in the pointer is offset by reducing the remaining index difference by one. If it is out of range, the induction endpoint likewise agrees with the claimed miss endpoint, since the index has advanced once and the remaining count has decreased once. In both cases, concatenate the initial segment with the inductive reach using transitivity of reachability ($\texttt{AReach.trans}$). The one-step reachability facts used for the initial test and probe steps are supplied by $\texttt{AReach.step}$ and $\texttt{AReach.single}$.

**Key facts.** `Complexity.LogProg.AReach.single`, `Complexity.LogProg.AReach.step`, `Complexity.LogProg.AReach.trans`, `Complexity.LogProg.arm_increments`, `Complexity.LogProg.register_update_le`.
