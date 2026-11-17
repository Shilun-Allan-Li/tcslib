<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/HastadSwitching.lean :: FABL.SwitchingBlockCode.card_finalOfSize -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Count of canonical codes of fixed size

**Claim.** The number of canonical width-$w$ switching block codes whose position set has size $i$ is $\binom{w}{i}2^i$.

**Proof.** Represent a canonical code by first choosing its position set $S$ of size $i$, then choosing a bit at each position in $S$. These choices give a bijection between canonical codes and the disjoint union, over all such $S$, of the functions from $S$ to the two-element bit field. For each $S$, there are $2^i$ such functions, so the total is the number of eligible position sets times $2^i$. The number of size-$i$ position sets among $w$ positions is $\binom{w}{i}$ (`FABL.SwitchingBlockCode.card_positionSet`), giving the claimed count.

**Key facts.** `FABL.SwitchingBlockCode.card_positionSet`.
