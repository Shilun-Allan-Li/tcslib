<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.graphMatchingTrace_partner_eq_on_remaining -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Partners Determined by the Pairing Trace

**Claim.** If two perfect matchings are closed on a remaining set of $2s$ vertices and their greedy pairing traces there agree, then they assign the same partner to every vertex in that set.

**Proof.** Proceed by induction on $s$. If $s=0$, the set is empty because its cardinality is zero, so there are no vertices whose partners need comparison.

For the inductive step, the common remaining set is nonempty. Its greedy pivot belongs to it. Each matching’s partner of that pivot also belongs to the set by closure, and lies in a different part from the pivot. Consequently each partner is an allowed first choice in the trace. The trace is a dependent pair: its first choice, followed by the trace on the set with the pivot and that chosen partner removed. Applying the successor trace equivalence to the assumed equality of traces shows that the two first choices agree. Hence the matchings give the pivot the same partner. Their partners are mutual by involutivity, so they also agree on the partner of this common partner.

After removing the pivot and its common partner, the remaining sets coincide, have cardinality $2s$, and are closed under each matching’s partner map. Equality of the original traces gives equality of the two tail traces on this common smaller set; the dependent tail types are aligned using the equality of the first choices. The induction hypothesis therefore gives equality of partners for every vertex in the smaller set. Every original vertex is either the pivot, its partner, or in the smaller set, completing the proof.

**Key facts.** `FABL.greedyPivot_mem`, `FABL.graphPartiteMatchingPartner_part_ne`, `FABL.graphMatchingClosedOn_erase_pair`, `FABL.graphPartiteMatchingPartner_involutive`.
