<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/Restrictions.lean :: FABL.disjoint_liftFreeFrequencyPart_liftFixedFrequencyPart -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Disjoint Lifted Frequency Parts

**Claim.** The frequencies in $U$ lying in $J$, lifted to the full coordinate set, are disjoint from the frequencies in $U$ outside $J$, lifted to the full coordinate set.

**Proof.** The two parts are obtained from a set of indices belonging to $J$ and a set of indices outside $J$, respectively. Apply the disjointness result for lifted free and fixed frequencies (`disjoint_liftFreeFrequency_liftFixedFrequency`) to these two parts.

**Key facts.** `FABL.disjoint_liftFreeFrequency_liftFixedFrequency`.
