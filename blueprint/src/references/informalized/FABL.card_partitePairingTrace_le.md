<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.card_partitePairingTrace_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Counting Partite Pairing Traces

**Claim.** For a set of $2s$ vertices in $2r$ parts, the number of pairing traces is at most $((2r-1)/r)^s s!$.

**Proof.** Proceed by induction on $s$. When $s=0$, the remaining set is empty, so there is exactly one trace, the empty trace, and the bound is $1$. For the step from $s$ to $s+1$, choose the greedy pivot in the nonempty remaining set. Every trace first chooses a partner from a different part and then continues with a trace on the set left after removing that pair. Thus the number of traces is the sum, over allowed partners, of the number of traces on the corresponding child set. Each child has $2s$ vertices, so the induction hypothesis bounds every summand by $((2r-1)/r)^s s!$. The number of allowed partners is at most $((2r-1)/r)(s+1)$, by the greedy partner-choice bound (`FABL.card_greedyPartnerChoices_le`). Multiplying these bounds gives $((2r-1)/r)^{s+1}(s+1)!$, as required. The pivot belongs to the remaining set (`FABL.greedyPivot_mem`), and each chosen partner is also in that set and lies in a different part, so removing the pair indeed leaves a set of size $2s$.

**Key facts.** `FABL.greedyPivot_mem`, `FABL.card_greedyPartnerChoices_le`.
