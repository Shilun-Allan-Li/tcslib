<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/Parse2.lean :: Complexity.LogProg.none_orElse' -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Left Identity for Option Choice

**Claim.** For any optional Boolean value $o$, choosing between no value and $o$ yields $o$.

**Proof.** By the definition of option choice, when the first option is absent the operation returns the second option. Hence $(\mathrm{none} <|> o)=o$.
