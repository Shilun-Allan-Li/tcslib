<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.mealyRun_keep -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Run with an identity transition

**Claim.** If each transition leaves both state and symbol unchanged, then running from $a$ on $w$ returns $(a,w)$.

**Proof.** Apply the Mealy-run induction principle (`mealyRun_induction`) to the property that the run on $w$ from state $b$ equals $(b,w)$. On the empty input this is immediate. For a first symbol $\gamma$, the identity transition returns state $b$ and symbol $\gamma$. The induction hypothesis gives the unchanged pair for the remaining input; consequently the full run returns $(b,\gamma::w)$, as required.

**Key facts.** `Turing.mealyRun_induction`.
