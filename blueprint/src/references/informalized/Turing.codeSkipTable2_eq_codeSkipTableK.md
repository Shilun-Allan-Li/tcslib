<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeSimulator.lean :: Turing.codeSkipTable2_eq_codeSkipTableK -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Equivalence of Table Readers

**Claim.** For every natural number $n$ and Boolean string $xs$, the table reader built from two work-field repetitions per action agrees with the iterated action reader using the corresponding setting.

**Proof.** The two sides unfold to the same expression by computation: in the definition of the iterated action reader, substituting the setting $k=2$ gives the four nested repetitions appearing in the two-work-field table reader. Thus the equality holds by reflexivity.
