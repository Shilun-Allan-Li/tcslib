<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean :: Complexity.macroCfg_setup -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Retargeting a Setup Configuration

**Claim.** Applying the macrostep construction to a setup configuration changes its phase and the specified unary-counter and guide head positions, while preserving the setup’s other data.

**Proof.** Compare the two configurations component by component. Their phases agree by the choice of the new phase, and their input-head positions, tape contents, and outputs agree because the macrostep construction preserves those components. For the work-head positions, split into the first $k$ tapes and the final three. The first $k$ positions are inherited from the base configuration on both sides. On the final three tapes, `finThree_cases` reduces the comparison to the base head, the unary-counter head, and the guide head: the base head remains $b$, while the other two are precisely the newly specified positions $u'$ and $g'$. All components therefore agree.

**Key facts.** `Complexity.finThree_cases`.
