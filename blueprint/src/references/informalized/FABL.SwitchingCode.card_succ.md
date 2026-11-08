<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/HastadSwitching.lean :: FABL.SwitchingCode.card_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Switching-Code Cardinality Recurrence

**Claim.** For all nonnegative integers $w$ and $k$, the number of switching codes of width $w$ and index $k+1$ equals $\binom{w}{k+1}2^{k+1}+\sum_{i=0}^{k-1}\binom{w}{i+1}(2^{i+1}-1)C(w,k-i)$, where $C(w,j)$ is the number of switching codes of width $w$ and index $j$.

**Proof.** Partition switching codes of index $k+1$ by their outer constructor. The final constructor contributes the number of canonical blocks with $k+1$ positions, which is $\binom{w}{k+1}2^{k+1}$ by the count of final blocks (`card_finalOfSize`). Each cons constructor is indexed by a choice $i$ among the $k$ positions; its block can be chosen in $\binom{w}{i+1}(2^{i+1}-1)$ ways by the count of full blocks (`card_fullOfSize`), and its tail is an arbitrary switching code of index $k-i$. Counting these independent choices by multiplication and summing over $i$ yields the recurrence.

**Key facts.** `FABL.SwitchingBlockCode.card_finalOfSize`, `FABL.SwitchingBlockCode.card_fullOfSize`.
