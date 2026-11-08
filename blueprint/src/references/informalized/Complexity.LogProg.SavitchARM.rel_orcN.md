<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/SavitchARM/Correct.lean :: Complexity.LogProg.SavitchARM.rel_orcN -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Encoded Step Relation Agreement

**Claim.** For a finite nondeterministic Turing machine, the oracle relation on two configuration codes and a window bound agrees with membership of the corresponding encoding in the machine’s step language.

**Proof.** Fix the two configuration codes and unfold the definitions of the oracle relation and the step relation. The oracle is the indicator function of the step language, so its value on the encoded input is true exactly when that input belongs to the language. By the definition of the indicator, this is equivalent to the corresponding membership proposition, which is precisely the step relation. Thus the two propositions agree for every pair of codes.

**Key facts.** `Complexity.LogProg.indicator_eq_decide`.
