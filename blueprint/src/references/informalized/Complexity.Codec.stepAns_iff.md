<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/StepDecider.lean :: Complexity.Codec.stepAns_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Boolean Step Test Characterization

**Claim.** Under the stated length and terminal-bit assumptions, the Boolean step test equals true exactly when the step-check predicate holds.

**Proof.** Expand both predicates. The characterization of valid configuration codes (`validChk_iff_pre`) replaces validity of $w$ by its precheck conditions together with acceptance of the scan of its configuration portion. The hypotheses already provide the precheck, while the scan-acceptance condition is precisely the initial Boolean factor in `stepAns`.

The remaining Boolean expression is a disjunction of two possibilities, one for each nondeterministic choice $b\in\{0,1\}$. A Boolean conjunction is true exactly when each of its factors is true, and a disjunction is true exactly when at least one branch is true. Thus truth of the expression supplies a choice $b$, the required input-head position equation, and the corresponding successful local scan; these are the remaining clauses of the step-check predicate. Conversely, a witness choice in that predicate selects the matching branch of the disjunction, and its equations make that branch true. The common scan-acceptance condition supplies the other required factor.

**Key facts.** `Complexity.Codec.validChk_iff_pre`.
