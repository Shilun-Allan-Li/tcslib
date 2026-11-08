<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/SpaceAmplifyPolyCode.lean :: Randomized.PolyAmp.accepting_congr -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Acceptance Under Configuration Equivalence

**Claim.** If two configurations have the same core data and output summary, then one is halted with output exactly $[\mathrm{true}]$ if and only if the other is.

**Proof.** Equality of the core sums implies equality of the state components, by projecting to the state coordinate. Equality of the second components gives equality of the output summaries. An output summary is the accepting summary exactly when the output list is $[\mathrm{true}]$ (`outSummary_eq_accept_iff`). Thus the two output lists are either both exactly $[\mathrm{true}]$ or both are not. Together with equality of states, this shows that the conditions defining acceptance agree for the two configurations.

**Key facts.** `Turing.outSummary_eq_accept_iff`.
